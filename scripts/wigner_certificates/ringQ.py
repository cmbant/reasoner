import sys, pickle, time
from sympy import QQ, symbols, Rational
from sympy.polys.rings import ring
from sympy.polys.fields import field
from sympy.polys.matrices import DomainMatrix
R, t,f,j2,j3,l1,l2,l3 = ring("t,f,j2,j3,l1,l2,l3", QQ)
def args(F):
    a=[t-F-j2-j3, t-F-l2-l3, t-l1-j2-l3, t-l1-l2-j3]
    b=[F+j2+l1+l2-t, j2+j3+l2+l3-t, j3+F+l3+l1-t]
    return a,b
a0,b0=args(f)
aref=[x+1 for x in a0]; bref=[b0[0]+1,b0[1],b0[2]+1]
def pm(x,xref):
    d=xref-x
    assert d.is_ground
    k=int(d.LC) if d else 0
    assert k>=0,(x,xref)
    m=R.one
    for i in range(1,k+1): m*=(x+i)
    return m
def mult(F):
    a,b=args(F); m=R.one
    for x,r in zip(a,aref): m*=pm(x,r)
    for x,r in zip(b,bref): m*=pm(x,r)
    return m
J=lambda x:x*(x+1)
D=(J(j3)+J(j2)-J(f))*(J(l3)+J(l2)-J(f))-2*(J(j3)*J(l3)+J(j2)*J(l2)-J(f)*J(l1))
rp=(f+1+j2-j3)*(f+1-j2+j3)*(f+1+l2-l3)*(f+1-l2+l3)
rm=(j2+j3+1-f)*(j2+j3+1+f)*(l2+l3+1-f)*(l2+l3+1+f)
t0=time.time()
L=(2*f+1)*D*mult(f)-f*rp*mult(f+1)-(f+1)*rm*mult(f-1)
print("lhs terms",len(L),time.time()-t0); sys.stdout.flush()
eas=[0,0,0,0]; ebs=[1,0,1]
a,b=args(f)
def sub_t1(p):  # p(t+1)
    return p.compose(t, t+1)
def Hm(h,shift):
    m=h if shift==0 else sub_t1(h)
    for x,e,r in zip(a,eas,aref): m*=pm(x+shift+e,r)
    for x,e,r in zip(b,ebs,bref): m*=pm(x-shift+e,r)
    fac=R((-1)**shift)
    for i in range(1,shift+1): fac*=(t+1+i)
    return fac*m
base=a[2]*a[3]
Es=[]
for k in range(3):
    h=base*t**k
    Es.append(Hm(h,1)-Hm(h,0))
    print("E",k,len(Es[-1])); sys.stdout.flush()
# coefficient extraction in t
def tcoeffs(p):
    d={}
    for mon,c in p.terms():
        e=mon[0]; m2=(0,)+mon[1:]
        d.setdefault(e,R.zero)
        d[e]=d[e]+R({m2:c})
    return d
cl=tcoeffs(L); ce=[tcoeffs(E) for E in Es]
degs=sorted(set(cl)|set().union(*[set(c) for c in ce]),reverse=True)
print("t-degrees",degs); sys.stdout.flush()
Kf,*gens=field("f,j2,j3,l1,l2,l3",QQ); K=Kf.to_domain(); gens=[K.convert(g) for g in gens]
def toK(p):
    # p ring elem with t-exponent 0
    res=K.zero
    for mon,c in p.terms():
        term=K(c)
        for g,e in zip(gens,mon[1:]): term*=g**e
        res+=term
    return res
rows=[[toK(ce[k].get(dg,R.zero)) for k in range(3)] for dg in degs]
rhs=[toK(cl.get(dg,R.zero)) for dg in degs]
M=DomainMatrix([[x for x in r] for r in rows],(len(degs),3),K)
bvec=DomainMatrix([[x] for x in rhs],(len(degs),1),K)
# solve least squares exactly: use first 3 independent rows via augmented rref
aug=M.hstack(bvec)
rr,piv=aug.rref()
print("pivots",piv); sys.stdout.flush()
rr=rr.to_Matrix() if hasattr(rr,'to_Matrix') else rr
import sympy as sp
sol=[sp.factor(rr[i,3]) for i in range(3)]
for i,s in enumerate(sol): print("q%d ="%i, s)
# check consistency: rows beyond rank must have zero rhs
print("consistent:", 3 in piv==False)
pickle.dump(sol,open('Qsol.pkl','wb'))
