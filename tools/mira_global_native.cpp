// Search-only port of the pinned Mira symbolic run-length executor.
// Every emitted candidate is still checked by the original Python and Coq.
#include <algorithm>
#include <cstdint>
#include <deque>
#include <vector>

struct Segment {
  int kind, b, a, c, mark;
  std::vector<int> effects;
  static Segment bit(int b) { return {0,b,0,1,-1,{}}; }
  static Segment run(int b,int a,int c) { return {1,b,a,c,-1,{}}; }
  static Segment box() { return {2,0,0,0,-1,{}}; }
};
struct Canon {
  int b,a,c;
  std::vector<int> effects;
  bool operator==(const Canon& x) const {
    return b==x.b && a==x.a && c==x.c && effects==x.effects;
  }
};
struct Case {
  std::deque<Segment> right;
  std::vector<Canon> expected;
  int branch;
  bool halt;
};
struct Context { std::vector<Case> cases; };

static std::vector<Canon> canon(const std::deque<Segment>& tape,bool left) {
  std::vector<Canon> out;
  for(const auto& s:tape) {
    if(s.kind==2) { out.push_back({2,s.mark,0,s.effects});continue; }
    int a=s.kind==0?0:s.a,c=s.kind==0?1:s.c;
    if(a==0 && c==0) continue;
    if(!out.empty() && out.back().b==s.b) {
      out.back().a+=a;out.back().c+=c;
    } else out.push_back({s.b,a,c,{}});
  }
  if(left) while(!out.empty() && out.back().b==0) out.pop_back();
  return out;
}

extern "C" {
void* mira_context_new() { return new Context(); }
void mira_context_delete(void* ptr) { delete static_cast<Context*>(ptr); }
int mira_add_case(void* ptr,const char* pc,int gap,int branch,int halt,
                  const int* expected,int length) {
  auto& ctx=*static_cast<Context*>(ptr);Case cs;int count=0;
  for(;pc[count];++count) cs.right.push_back(Segment::bit(pc[count]-'0'));
  cs.right.push_back(Segment::run(0,1,gap-count));
  cs.right.push_back(Segment::bit(1));cs.right.push_back(Segment::box());
  cs.branch=branch;cs.halt=halt;
  for(int i=0;i<length;++i) {
    int b=expected[3*i],a=expected[3*i+1],c=expected[3*i+2];
    if(b==2) {
      Canon x={2,-1,0,{}};
      if(a) x.effects.push_back(a*16+c);
      cs.expected.push_back(x);
    } else cs.expected.push_back({b,a,c,{}});
  }
  ctx.cases.push_back(std::move(cs));return (int)ctx.cases.size()-1;
}

// fixed = dispatch96, exit2, exit6, inc73, dec43, exit48, exit3, exit63.
int mira_run_case(void* ptr,const int* table,int n,const int* skip,
                  const int* fixed,int case_id,int fuel,uint8_t* observed) {
  auto& ctx=*static_cast<Context*>(ptr);
  if(case_id<0 || case_id>=(int)ctx.cases.size()) return 0;
  const auto& cs=ctx.cases[case_id];
  std::deque<Segment> L{Segment::bit(1)},R=cs.right;
  int q=fixed[0],form=0,steps=0;
  const std::vector<Canon> marker{{1,0,1,{}}};
  auto edge=[&](int bit,int& w,int& d,int& t) {
    if(q<0 || q>=n) return false;
    if(observed) observed[2*q+bit]=1;
    const int* e=table+6*q+3*bit;w=e[0];d=e[1];t=e[2];
    return (w==0 || w==1) && (d==1 || d==-1) && t>=-1;
  };
  while(fuel-->0) {
    if(q==-1) return cs.halt;
    if(q<0 || q>=n) return 0;
    if(form==0 && q==fixed[0] && steps>0 && canon(L,true)==marker && canon(R,false)==cs.expected)
      return !cs.halt;
    if(form==1) {
      if(L.empty()) { R.push_front(Segment::bit(0));form=0;continue; }
      Segment s=L.front();
      if(s.kind==0) { L.pop_front();R.push_front(s);form=0;continue; }
      if(s.kind!=1) return 0;
      int w,d,t;if(!edge(s.b,w,d,t)) return 0;
      if(d==-1 && t==q) {
        L.pop_front();R.push_front(Segment::run(w,s.a,s.c));++steps;continue;
      }
      if(s.c>=1) {
        L.pop_front();if(s.a!=0 || s.c-1!=0)L.push_front(Segment::run(s.b,s.a,s.c-1));
        R.push_front(Segment::bit(s.b));form=0;continue;
      }
      if(s.a==0) { L.pop_front();continue; }
      return 0;
    }
    if(R.empty()) return 0;
    Segment s=R.front();
    if(s.kind==0) {
      int w,d,t;if(!edge(s.b,w,d,t)) return 0;++steps;
      if(d==1) { L.push_front(Segment::bit(w));R.pop_front(); }
      else { R.front()=Segment::bit(w);form=1; }
      q=t;continue;
    }
    if(s.kind==1) {
      int w,d,t;if(!edge(s.b,w,d,t)) return 0;
      if(d==1 && t==q) {
        L.push_front(Segment::run(w,s.a,s.c));R.pop_front();++steps;continue;
      }
      if(s.c>=1) {
        R.pop_front();if(s.a!=0 || s.c-1!=0)R.push_front(Segment::run(s.b,s.a,s.c-1));
        R.push_front(Segment::bit(s.b));continue;
      }
      if(s.a==0) { R.pop_front();continue; }
      return 0;
    }
    if(skip[q]>=0 && s.mark<0) {
      int r=skip[q];R.front().mark=r;q=r==0?fixed[1]:fixed[2];form=1;++steps;continue;
    }
    if(q==fixed[3] && s.mark>=0) {
      R.front().mark=-1;R.front().effects.push_back(16+s.mark);
      q=fixed[5];form=1;++steps;continue;
    }
    if(q==fixed[4] && s.mark>=0) {
      R.front().mark=-1;
      if(cs.branch==1) { R.front().effects.push_back(48+s.mark);q=fixed[6]; }
      else { R.front().effects.push_back(32+s.mark);q=s.mark==0?fixed[7]:fixed[5]; }
      form=1;++steps;continue;
    }
    int w,d,t;if(!edge(0,w,d,t)) return 0;
    if(w==0 && d==-1) { q=t;form=1;++steps;continue; }
    return 0;
  }
  return 0;
}
}
