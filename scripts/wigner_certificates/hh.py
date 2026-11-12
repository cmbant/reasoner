from fractions import Fraction as Fr
from math import factorial
def ifa(x):
    x=Fr(x)
    if x.denominator!=1 or x<0: return Fr(0)
    return Fr(1,factorial(int(x)))
def T(F,t,j2,j3,l1,l2,l3):
    return (-1)**t*(factorial(t+1) if t>=-1 else 0)*ifa(t-F-j2-j3)*ifa(t-F-l2-l3)*ifa(t-l1-j2-l3)*ifa(t-l1-l2-j3)*ifa(F+j2+l1+l2-t)*ifa(j2+j3+l2+l3-t)*ifa(j3+F+l3+l1-t)
f,j2,j3,l1,l2,l3=12,10,11,9,8,13
J=lambda x:x*(x+1)
D=(J(j3)+J(j2)-J(f))*(J(l3)+J(l2)-J(f))-2*(J(j3)*J(l3)+J(j2)*J(l2)-J(f)*J(l1))
rp=(f+1+j2-j3)*(f+1-j2+j3)*(f+1+l2-l3)*(f+1-l2+l3)
rm=(j2+j3+1-f)*(j2+j3+1+f)*(l2+l3+1-f)*(l2+l3+1+f)
def Fn(t): return (2*f+1)*D*T(f,t,j2,j3,l1,l2,l3)-f*rp*T(f+1,t,j2,j3,l1,l2,l3)-(f+1)*rm*T(f-1,t,j2,j3,l1,l2,l3)
H=Fr(0)
for t in range(0,40):
    ft=Fn(t); 
    print(t,ft,H,T(f,t,j2,j3,l1,l2,l3), (H/T(f,t,j2,j3,l1,l2,l3) if T(f,t,j2,j3,l1,l2,l3)!=0 else None))
    H+=ft
print("----")
def Bref(t,ea,eb):
    F=f
    a=[t-F-j2-j3, t-F-l2-l3, t-l1-j2-l3, t-l1-l2-j3]
    b=[F+j2+l1+l2-t, j2+j3+l2+l3-t, j3+F+l3+l1-t]
    r=(-1)**t*(factorial(t+1) if t>=-1 else 0)
    for x in a: r*=ifa(x+ea)
    for x in b: r*=ifa(x+eb)
    return r
H=Fr(0); data={}
for t in range(0,60):
    data[t]=H
    H+=Fn(t)
for ea,eb in [(-1,0),(-1,-1),(0,-1),(-2,0),(-1,1),(0,1)]:
    pts=[(t,data[t]/Bref(t,ea,eb)) for t in range(0,60) if Bref(t,ea,eb)!=0]
    ys=[y for _,y in pts]
    # finite differences
    d=ys[:]
    degs=[]
    for k in range(8):
        d=[d[i+1]-d[i] for i in range(len(d)-1)]
        if d and all(x==0 for x in d): degs.append(k); break
    print(ea,eb,len(pts),degs, ys[:4])
print("=====")
import sympy as sp
exec(open('cert6j.py').read().split("a,b=args(f)\n# H(t)")[0])
vals={sp.Symbol('f'):f,sp.Symbol('j2'):j2,sp.Symbol('j3'):j3,sp.Symbol('l1'):l1,sp.Symbol('l2'):l2,sp.Symbol('l3'):l3}
for tt in range(30,41):
    U=Bref(tt,1,1)
    lv=lhs.subs(vals).subs(sp.Symbol('t'),tt)
    print(tt, Fn(tt), Fr(int(lv.p),int(lv.q))*U)
