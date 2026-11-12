import sympy as sp, sys, pickle
t,f,j2,j3,l1,l2,l3=sp.symbols('t f j2 j3 l1 l2 l3')
def args(F):
    a=[t-F-j2-j3, t-F-l2-l3, t-l1-j2-l3, t-l1-l2-j3]
    b=[F+j2+l1+l2-t, j2+j3+l2+l3-t, j3+F+l3+l1-t]
    return a,b
REF=4
a0,b0=args(f)
aref=[x+REF for x in a0]; bref=[x+REF for x in b0]
def poly_mult(x,xref):
    k=int(sp.simplify(xref-x)); assert k>=0
    m=sp.Integer(1)
    for i in range(1,k+1): m*=(x+i)
    return m
def mult(F):
    a,b=args(F); m=sp.Integer(1)
    for x,r in zip(a,aref): m*=poly_mult(x,r)
    for x,r in zip(b,bref): m*=poly_mult(x,r)
    return m
J=lambda x:x*(x+1)
J2=j2*(j2+1);J3=j3*(j3+1);L2=l2*(l2+1);L3=l3*(l3+1);L1=l1*(l1+1)
D=(J3+J2-J(f))*(L3+L2-J(f))-2*(J3*L3+J2*L2-J(f)*L1)
rp=(f+1+j2-j3)*(f+1-j2+j3)*(f+1+l2-l3)*(f+1-l2+l3)
rm=(j2+j3+1-f)*(j2+j3+1+f)*(l2+l3+1-f)*(l2+l3+1+f)
lhs=(2*f+1)*D*mult(f)-f*rp*mult(f+1)-(f+1)*rm*mult(f-1)
eas=[0,0,0,0]; ebs=[1,0,1]
def Hmult(h,shift):
    a,b=args(f); m=h.subs(t,t+shift)
    for x,e,r in zip(a,eas,aref): m*=poly_mult(x+shift+e,r)
    for x,e,r in zip(b,ebs,bref): m*=poly_mult(x-shift+e,r)
    fac=sp.Integer((-1)**shift)
    for i in range(1,shift+1): fac*=(t+1+i)
    return fac*m
a,b=args(f)
q0,q1,q2=sp.symbols('q0 q1 q2')
h=a[2]*a[3]*(q2*t**2+q1*t+q0)
expr=lhs-(Hmult(h,1)-Hmult(h,0))
P=sp.Poly(sp.expand(expr),t)
co=P.all_coeffs()
print(len(co)); sys.stdout.flush()
# top coefficient eqs are linear in q's
sol=sp.solve(co[:6],[q0,q1,q2],dict=True)
print(sol); sys.stdout.flush()
s={k:sp.factor(v) for k,v in sol[0].items()}
for k,v in s.items(): print(k,v)
pickle.dump(s,open('Q.pkl','wb'))
res=[sp.expand(c.subs(s)) for c in co]
print("residual zero:",all(r==0 for r in res))
