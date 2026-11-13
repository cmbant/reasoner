import pickle,sympy as sp, time
s,j1,j2,j3,m1,m2=sp.symbols('s j1 j2 j3 m1 m2')
a1,a2,a3,b1,b2,b3=sp.symbols('a1 a2 a3 b1 b2 b3')
q=pickle.load(open('Q3j.pkl','rb'))
def args(J):
    A=[s, j3-j2+m1+s, j3-J-m2+s]; B=[J+j2-j3-s, J-m1-s, j2+m2-s]; return A,B
A0,B0=args(j1)
Aref=[x+1 for x in A0]; Bref=[x+1 for x in B0]
def pm(x,r):
    k=int(sp.simplify(r-x)); m=1
    for i in range(1,k+1): m*=(x+i)
    return m
def mult(J):
    A,B=args(J); m=1
    for x,r in zip(A,Aref): m*=pm(x,r)
    for x,r in zip(B,Bref): m*=pm(x,r)
    return m
A,B=args(j1)
def Hm(shift,eas,ebs):
    m=1
    for x,e,r in zip(A,eas,Aref): m*=pm(x+shift+e,r)
    for x,e,r in zip(B,ebs,Bref): m*=pm(x-shift+e,r)
    return m
Jj=lambda x:x*(x+1)
m3=-m1-m2
C=(2*j1+1)*((Jj(j2)-Jj(j3))*m1-Jj(j1)*(m3-m2))
rp=(j1+1+j2-j3)*(j1+1-j2+j3)*(j1+1+m1)*(j1+1-m1)
rm=(j2+j3+1-j1)*(j1+j2+j3+1)
Q0=lambda S: (q[2]*S**2+q[1]*S+q[0])
h0=lambda S: S*(j3-j2+m1+S)*Q0(S)
Lside=[C*mult(j1),(j1+1)*rm*mult(j1-1),j1*rp*mult(j1+1)]
Rside=[h0(s+1)*Hm(1,[0]*3,[1,1,0]), h0(s)*Hm(0,[0]*3,[1,1,0])]
print("orig counts",[len(sp.Poly(sp.expand(e),s,j1,j2,j3,m1,m2).terms()) for e in Lside+Rside])
# atoms: solve for params in terms of atoms
sol=sp.solve([a1-s,a2-(j3-j2+m1+s),a3-(j3-j1-m2+s),b1-(j1+j2-j3-s),b2-(j1-m1-s),b3-(j2+m2-s)],[s,j1,j2,j3,m1,m2],dict=True)[0]
print(sol)
sub=lambda e: sp.expand(e.subs(sol))
cnt=[]
for e in Lside+Rside:
    ee=sub(e); cnt.append(len(sp.Poly(ee,a1,a2,a3,b1,b2,b3).terms()))
print("atom counts",cnt)
Qa=sub(Q0(s))
print("Q atoms terms",len(sp.Poly(Qa,a1,a2,a3,b1,b2,b3).terms()))
print(sp.factor(Qa))
