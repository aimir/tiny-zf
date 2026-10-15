"""Compiled search filter; never substitutes for the pinned Python/Coq gates."""
import ctypes
from collections import defaultdict
from pathlib import Path
from mira_global import SKIP,state_key


class Engine:
    """Cache symbolic cases and evaluate arbitrary table/case subsets in C++."""
    def __init__(self,library,max_cases=32768):
        if type(max_cases) is not int or max_cases<1:
            raise ValueError('max_cases must be a positive integer')
        self.max_cases=max_cases
        self.lib=ctypes.CDLL(str(Path(library).resolve()))
        self.lib.mira_context_new.restype=ctypes.c_void_p
        self.lib.mira_context_delete.argtypes=[ctypes.c_void_p]
        self.lib.mira_add_case.argtypes=[ctypes.c_void_p,ctypes.c_char_p,ctypes.c_int,
            ctypes.c_int,ctypes.c_int,ctypes.POINTER(ctypes.c_int),ctypes.c_int]
        self.lib.mira_add_case.restype=ctypes.c_int
        self.lib.mira_run_case.argtypes=[ctypes.c_void_p,ctypes.POINTER(ctypes.c_int),
            ctypes.c_int,ctypes.POINTER(ctypes.c_int),ctypes.POINTER(ctypes.c_int),
            ctypes.c_int,ctypes.c_int,ctypes.POINTER(ctypes.c_uint8)]
        self.lib.mira_run_case.restype=ctypes.c_int
        self.context=self.lib.mira_context_new();self.cache={};self.identity={};self.names=[];self.ids={}

    def close(self):
        if self.context:self.lib.mira_context_delete(self.context);self.context=None
        self.cache.clear();self.identity.clear()

    def clear_cases(self):
        """Release old layouts' Python/C++ cases; keep the configured machine."""
        self.close()
        self.context=self.lib.mira_context_new()

    def __del__(self):
        if getattr(self,'context',None):self.close()

    def add_case(self,case):
        cached=self.identity.get(id(case))
        if cached is not None and cached[0] is case:return cached[1]
        tape,branch,expected,want=case
        key=tuple(tape),branch,expected,want
        if key in self.cache:
            index=self.cache[key]
            if len(self.identity)>=65536:self.identity.clear()
            self.identity[id(case)]=(case,index)
            return index
        if len(self.cache)>=self.max_cases:self.clear_cases()
        pc=[];i=0
        while i<len(tape) and tape[i][0]=='b':pc.append(str(tape[i][1]));i+=1
        if (len(tape)!=i+3 or tape[i][:3]!=('r',0,1) or
                tape[i+1:]!=[('b',1),('box',('plain',))] or expected[0]!=((1,0,1),)):
            raise ValueError('unsupported symbolic instruction boundary')
        gap=tape[i][3]+len(pc);flat=[]
        effect=dict(inc=1,dec=2,dec0=3)
        for segment in expected[1]:
            if segment[0]=='box':
                box=segment[1]
                if box[0]!='plain' or len(box)>2:raise ValueError('unsupported expected box')
                flat.extend((2,effect[box[1][0]],box[1][1]) if len(box)==2 else (2,0,0))
            else:flat.extend(segment)
        values=(ctypes.c_int*len(flat))(*flat)
        index=self.lib.mira_add_case(self.context,''.join(pc).encode(),gap,
            {'-':0,'z':1,'p':2}[branch],int(want=='halt'),values,len(flat)//3)
        self.cache[key]=index
        if len(self.identity)>=65536:self.identity.clear()
        self.identity[id(case)]=(case,index)
        return index

    def configure(self,table):
        extra=sorted({q for q,b in table}-self.ids.keys(),key=state_key)
        for q in extra:self.ids[q]=len(self.names);self.names.append(q)
        self.n=len(self.names)
        self.buffer=(ctypes.c_int*(6*self.n))(*([-2]*(6*self.n)))
        for key,edge in table.items():self.set_edge(key,edge)
        skip=[-1]*self.n
        for q,r in SKIP.items():
            if q in self.ids:skip[self.ids[q]]=r+1
        self.skip=(ctypes.c_int*self.n)(*skip)
        self.fixed=(ctypes.c_int*8)(*(self.ids[q] for q in ('96','2','6','73','43','48','3','63')))

    def set_edge(self,key,edge):
        q,b=key;w,d,t=edge;offset=6*self.ids[q]+3*b
        self.buffer[offset:offset+3]=[w,1 if d=='R' else -1,
            -1 if t=='254' else self.ids.get(t,-2)]

    def run_case(self,case,trace=None):
        # add_case may replace the C context when its cache is full. Obtain the
        # index before evaluating the context argument, avoiding a freed pointer.
        index=self.add_case(case)
        return bool(self.lib.mira_run_case(self.context,self.buffer,self.n,self.skip,
            self.fixed,index,2000,trace))

    def check_cases(self,table,cases,indices=None):
        self.configure(table)
        for i in range(len(cases)) if indices is None else indices:
            if not self.run_case(cases[i]):return False,i
        return True,None

    def traces(self,table,cases):
        self.configure(table);by_edge=defaultdict(list)
        for i,case in enumerate(cases):
            trace=(ctypes.c_uint8*(2*self.n))()
            if not self.run_case(case,trace):raise ValueError(f'native baseline failed case {i}')
            for k,used in enumerate(trace):
                if used:by_edge[self.names[k//2],k%2].append(i)
        return by_edge


class NativeOracle:
    """Drop-in mutation filter built from a Python Oracle's explicit cases."""
    def __init__(self,python_oracle,library):
        self.python_oracle=python_oracle
        self.d0=python_oracle.d0
        self.engine=Engine(library);self.cases=python_oracle.cases
        self.tree=python_oracle.tree;self.root=python_oracle.root
        self.directory=python_oracle.directory;self.protected=python_oracle.protected
        self.mutable_anchor_rows=python_oracle.mutable_anchor_rows
        self.trials=0;self.rebase(python_oracle.table)

    def rebase(self,table):
        self.table=table;self.by_edge=self.engine.traces(table,self.cases)

    def check(self,table):
        try:return self.engine.check_cases(table,self.cases)
        finally:self.engine.configure(self.table)

    def confirm(self,table):
        """Independent final filter using the pinned Python implementation."""
        return self.python_oracle.check(table)

    def check_edge(self,key,edge):
        original=self.table[key];self.engine.set_edge(key,edge);self.trials+=1
        affected=self.by_edge[key]
        try:
            for j,i in enumerate(affected):
                if not self.engine.run_case(self.cases[i]):
                    if j:affected.insert(0,affected.pop(j))
                    return False
            return True
        finally:self.engine.set_edge(key,original)
