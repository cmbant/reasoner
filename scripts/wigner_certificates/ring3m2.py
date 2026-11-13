import sympy as sp
s,j1,j2,j3,m1,m2=sp.symbols('s j1 j2 j3 m1 m2')
def args(M):
    A=[s, j3-j2+m1+s, j3-j1-M+s]; B=[j1+j2-j3-s, j1-m1-s, j2+M-s]; return A,B
A0,B0=args(m2)
Aref=[A0[0],A0[1],A0[2]+1]; Bref=[B0[0],B0[1],B0[2]+1]
def pm(x,r):
    k=int(sp.simplify(r-x)); assert k>=0,(x,r)
    m=1
    for i in range(1,k+1): m*=(x+i)
    return m
def mult(M):
    A,B=args(M); m=1
    for x,r in zip(A,Aref): m*=pm(x,r)
    for x,r in zip(B,Bref): m*=pm(x,r)
    return m
J=lambda x:x*(x+1); m3=-m1-m2
C=J(j1)-J(j2)-J(j3)-2*m2*m3
rp=(j2+m2+1)*(j3-m3+1); rm=(j2-m2+1)*(j3+m3+1)
print("m0",sp.factor(mult(m2)));print("m+",sp.factor(mult(m2+1)));print("m-",sp.factor(mult(m2-1)))
A,B=args(m2)
eas=[-1,-1,0]; ebs=[0,0,1]
def Hm(shift):
    m=1
    for x,e,r in zip(A,eas,Aref): m*=pm(x+shift+e,r)
    for x,e,r in zip(B,ebs,Bref): m*=pm(x-shift+e,r)
    return (-1)**shift*m
print("H0",sp.factor(Hm(0)));print("H1",sp.factor(Hm(1)))
c=sp.symbols('c')
L=sp.expand(C*mult(m2)+rp*mult(m2+1)+rm*mult(m2-1))
E=sp.expand(Hm(1)-Hm(0))
sol=sp.solve(sp.Poly(sp.expand(L-c*E),s).all_coeffs(),c,dict=True)
print(sol)
if sol: print(sp.factor(sol[0][c]))
