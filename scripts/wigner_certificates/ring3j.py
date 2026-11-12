import sys, pickle, time
from sympy import QQ
import sympy as sp
from sympy.polys.rings import ring
from sympy.polys.fields import field
from sympy.polys.matrices import DomainMatrix
R, s,j1,j2,j3,m1,m2 = ring("s,j1,j2,j3,m1,m2", QQ)
def args(J):
    A=[s, j3-j2+m1+s, j3-J-m2+s]
    B=[J+j2-j3-s, J-m1-s, j2+m2-s]
    return A,B
A0,B0=args(j1)
Aref=[x+1 for x in A0]; Bref=[x+1 for x in B0]
def pm(x,xr):
    d=xr-x; assert d.is_ground
    k=int(d.LC) if d else 0; assert k>=0,(x,xr)
    m=R.one
    for i in range(1,k+1): m*=(x+i)
    return m
def mult(J):
    A,B=args(J); m=R.one
    for x,r in zip(A,Aref): m*=pm(x,r)
    for x,r in zip(B,Bref): m*=pm(x,r)
    return m
Jj=lambda x:x*(x+1)
m3=-m1-m2
C=(2*j1+1)*((Jj(j2)-Jj(j3))*m1-Jj(j1)*(m3-m2))
rp=(j1+1+j2-j3)*(j1+1-j2+j3)*(j1+1+m1)*(j1+1-m1)
rm=(j2+j3+1-j1)*(j1+j2+j3+1)
L=C*mult(j1)+(j1+1)*rm*mult(j1-1)+j1*rp*mult(j1+1)
print("L terms",len(L)); sys.stdout.flush()
eas=[0,0,0]; ebs=[1,1,0]
A,B=args(j1)
def Hm(h,shift):
    m=h if shift==0 else h.compose(s,s+1)
    for x,e,r in zip(A,eas,Aref): m*=pm(x+shift+e,r)
    for x,e,r in zip(B,ebs,Bref): m*=pm(x-shift+e,r)
    return R((-1)**shift)*m
# h = s * (105 s + 101)-like: ansatz s*(c0 + c1 s + c2 s^2)... eas=(0,0,0) => h = s*(lin)*quad  (deg 4) ; use h = s*(A2)* (q0+q1 s+q2 s^2)?
# From numeric: (0,0,0),(1,1,0): h = -s*(105 s+101)*(quad)/588000 ; 105 s+101 ~ A2+1? A2 = j3-j2+m1+s
base=A[0]*A[1]
Es=[]
for k in range(3):
    h=base*s**k
    Es.append(Hm(h,1)-Hm(h,0))
def tcoeffs(p):
    d={}
    for mon,c in p.terms():
        e=mon[0]; m2_=(0,)+mon[1:]
        d.setdefault(e,R.zero); d[e]=d[e]+R({m2_:c})
    return d
cl=tcoeffs(L); ce=[tcoeffs(E) for E in Es]
degs=sorted(set(cl)|set().union(*[set(c) for c in ce]),reverse=True)
Kf,*gens=field("j1,j2,j3,m1,m2",QQ); K=Kf.to_domain(); gens=[K.convert(g) for g in gens]
def toK(p):
    res=K.zero
    for mon,c in p.terms():
        term=K(c)
        for g,e in zip(gens,mon[1:]): term*=g**e
        res+=term
    return res
rows=[[toK(ce[k].get(dg,R.zero)) for k in range(3)] for dg in degs]
rhs=[toK(cl.get(dg,R.zero)) for dg in degs]
M=DomainMatrix(rows,(len(degs),3),K); bv=DomainMatrix([[x] for x in rhs],(len(degs),1),K)
rr,piv=M.hstack(bv).rref(); print("pivots",piv)
rr=rr.to_Matrix()
sol=[sp.factor(rr[i,3]) for i in range(3)]
for i,x in enumerate(sol): print("q%d ="%i, x)
print("consistent:", 3 not in piv)
pickle.dump(sol,open('Q3j.pkl','wb'))
