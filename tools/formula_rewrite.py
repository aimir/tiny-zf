"""Classical formula rewrites for the five protected schemas only.

Logical axioms and inference rules remain unchanged. Conjunction/disjunction
are represented in negation normal form; choosing child order changes the
emitted ->/not expression while preserving its truth function. Quantifiers
are kept in their original scope, using exists = not forall not.
"""
from ics import RPN


def parse(text):
    stack=[]
    for token in text.split():
        if token in ('p1','p2','p3'):stack.append(token)
        elif token=='wn':
            if not stack:raise ValueError('missing negation operand')
            stack.append((token,stack.pop()))
        else:
            if token not in ('weq','wel','wim','wa','wal','wex'):
                raise ValueError('unknown formula token: '+token)
            if len(stack)<2:raise ValueError('missing binary operand')
            b=stack.pop();a=stack.pop();stack.append((token,a,b))
    if len(stack)!=1:raise ValueError('bad expression')
    return stack[0]


def nnf(t,negative=False):
    if isinstance(t,str) or t[0] in ('weq','wel'):
        return ('lit',negative,t)
    op,*xs=t
    if op=='wn':return nnf(xs[0],not negative)
    a,b=xs
    if op in ('wal','wex'):
        universal=(op=='wal')!=negative
        return ('all' if universal else 'exists',a,nnf(b,negative))
    if op=='wim':
        return ('and' if negative else 'or',nnf(a,not negative),nnf(b,negative))
    if op=='wa':return ('or' if negative else 'and',nnf(a,negative),nnf(b,negative))
    raise ValueError(op)


def negate(t):
    return t[1] if isinstance(t,tuple) and t[0]=='wn' else ('wn',t)


def lower(t,choices,position=None):
    if position is None:position=[0]
    if t[0]=='lit':return negate(t[2]) if t[1] else t[2]
    if t[0] in ('all','exists'):
        body=lower(t[2],choices,position)
        return ('wal',t[1],body) if t[0]=='all' else negate(('wal',t[1],negate(body)))
    index=position[0];position[0]+=1
    a=lower(t[1],choices,position);b=lower(t[2],choices,position)
    if choices&(1<<index):a,b=b,a
    if t[0]=='or':return ('wim',negate(a),b)
    return negate(('wim',a,negate(b)))


def tokens(t):
    if isinstance(t,str):return [t]
    if t[0]=='wn':
        child=t[1]
        if isinstance(child,tuple) and child[0] in ('wal','wim'):
            right=child[2]
            if isinstance(right,tuple) and right[0]=='wn':
                op='wex' if child[0]=='wal' else 'wa'
                return [*tokens(child[1]),*tokens(right[1]),op]
        return [*tokens(child),'wn']
    return [*tokens(t[1]),*tokens(t[2]),t[0]]


def choices_count(t):
    if t[0]=='lit':return 0
    if t[0] in ('all','exists'):return choices_count(t[2])
    return 1+choices_count(t[1])+choices_count(t[2])


LIMITS = {name: 1 << choices_count(nnf(parse(source)))
          for name, source in RPN.items()}


def validate_choices(choices):
    """Reject unknown schemas and bits that do not select a Boolean node."""
    if not isinstance(choices, dict):
        raise ValueError('formula choices must be a dictionary')
    for name, value in choices.items():
        if name not in LIMITS or type(value) is not int or not 0 <= value < LIMITS[name]:
            raise ValueError('invalid protected-formula choice')


def rewrite(source, choice):
    """Emit a selected NNF expression using the source constructor vocabulary."""
    return ' '.join(tokens(lower(nnf(parse(source)), choice)))


class RewrittenFormulas:
    rewrite_choices={}
    def constructor_sequence(self,source,permutation):
        # Only the protected set-theory/freshness clauses are rewritten.
        for name,original in RPN.items():
            if source==original and name in self.rewrite_choices:
                source=rewrite(source,self.rewrite_choices[name])
                break
        return super().constructor_sequence(source,permutation)


class BooleanForms:
    """Reduced ordered BDDs, treating equal quantified bodies congruently.

    Quantifiers are opaque unary operators indexed by their variable; their
    bodies must already have identical canonical Boolean forms. This permits
    propositional equivalence and quantifier congruence, not arbitrary changes
    of quantifier order, scope, or equality/membership atoms.
    """
    def __init__(self):
        self.variables={};self.nodes={};self.unique={};self.cache={}

    def node(self,var,lo,hi):
        if lo==hi:return lo
        key=(var,lo,hi)
        if key not in self.unique:
            idx=len(self.nodes)+2;self.nodes[idx]=key;self.unique[key]=idx
        return self.unique[key]

    def atom(self,key):
        if key not in self.variables:self.variables[key]=len(self.variables)
        return self.node(self.variables[key],0,1)

    def apply(self,op,a,b=0):
        key=(op,a,b)
        if key in self.cache:return self.cache[key]
        if a<2 and b<2:
            result=int(not a) if op=='not' else int((not a) or b) if op=='imp' else int(a and b)
        else:
            top=min(self.nodes[a][0] if a>=2 else float('inf'),self.nodes[b][0] if b>=2 else float('inf'))
            def children(x):
                return self.nodes[x][1:] if x>=2 and self.nodes[x][0]==top else (x,x)
            al,ah=children(a);bl,bh=children(b)
            result=self.node(top,self.apply(op,al,bl),self.apply(op,ah,bh))
        self.cache[key]=result
        return result

    def formula(self,t):
        if isinstance(t,str):return self.atom(('parameter',t))
        op,*xs=t
        if op in ('weq','wel'):return self.atom(t)
        if op=='wn':return self.apply('not',self.formula(xs[0]))
        if op=='wim':return self.apply('imp',self.formula(xs[0]),self.formula(xs[1]))
        if op=='wa':return self.apply('and',self.formula(xs[0]),self.formula(xs[1]))
        var,body=xs
        if op=='wal':return self.atom(('forall',var,self.formula(body)))
        if op=='wex':return self.apply('not',self.atom(('forall',var,self.apply('not',self.formula(body)))))
        raise ValueError(op)


def check_rewrite(source,rewritten):
    forms=BooleanForms()
    a=forms.formula(parse(source));b=forms.formula(parse(rewritten))
    if a!=b:raise ValueError('formulas differ under Boolean/quantifier-congruence check')
    return {'atoms':len(forms.variables),'bdd_nodes':len(forms.nodes)}


def check_choices(choices):
    """Independently check each selected formula before parameter renaming.

    The checker does not use NNF or the lowering algorithm: it interprets both
    RPN expressions directly as Boolean functions with congruent quantifiers.
    This is a computational certificate, not a Lean derivation in the source
    Hilbert calculus. Logical axiom schemas and inference rules are unchanged.
    """
    validate_choices(choices)
    return {name: {'choice': choice, 'rpn': rewrite(RPN[name], choice),
                   **check_rewrite(RPN[name], rewrite(RPN[name], choice))}
            for name, choice in choices.items()}
