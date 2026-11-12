import sympy as sp, itertools, sys
s=sp.symbols('s'); R=sp.Rational
j1,j2,j3,m1,m2=R(7,2),R(5,3),R(11,5),R(3,7),R(13,4)
def args(M):
    A=[s, j3-j2+m1+s, j3-j1-M+s]; B=[j1+j2-j3-s, j1-m1-s, j2+M-s]; return A,B
A0,B0=args(m2)
Aref=[x+1 for x in A0]; Bref=[x+1 for x in B0]
def pmul(x,xr):
    k=int(sp.simplify(xr-x)); assert k>=0
    m=1
    for i in range(1,k+1): m*=(x+i)
    return m
def mult(M):
    A,B=args(M); m=1
    for x,r in zip(A,Aref): m*=pmul(x,r)
    for x,r in zip(B,Bref): m*=pmul(x,r)
    return m
J=lambda x:x*(x+1); m3=-m1-m2
C=J(j1)-J(j2)-J(j3)-2*m2*m3
rp=(j2+m2+1)*(j3-m3+1); rm=(j2-m2+1)*(j3+m3+1)
# NOTE: m2->m2+1 shifts A3 by -1 and B3 by +1 ; our args() handles it
L=sp.expand(C*mult(m2)+rp*mult(m2+1)+rm*mult(m2-1))
A,B=args(m2)
d=int(sys.argv[1]) if len(sys.argv)>1 else 4
cs=sp.symbols('c0:%d'%(d+1)); h=sum(c*s**i for i,c in enumerate(cs))
def Hm(h,eas,ebs,shift):
    m=h.subs(s,s+shift)
    for x,e,r in zip(A,eas,Aref): m*=pmul(x+shift+e,r)
    for x,e,r in zip(B,ebs,Bref): m*=pmul(x-shift+e,r)
    return (-1)**shift*m
for eas in itertools.product([-1,0,1],repeat=3):
  for ebs in itertools.product([-1,0,1],repeat=3):
    try: expr=sp.expand(L-(Hm(h,eas,ebs,1)-Hm(h,eas,ebs,0)))
    except AssertionError: continue
    sol=sp.solve(sp.Poly(expr,s).all_coeffs(),cs,dict=True)
    if sol: print("FOUND",eas,ebs,sp.factor(h.subs(sol[0]))); sys.stdout.flush()
print("done")
