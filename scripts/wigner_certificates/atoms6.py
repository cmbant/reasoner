import pickle,sympy as sp,time
t,f,j2,j3,l1,l2,l3=sp.symbols('t f j2 j3 l1 l2 l3')
A1,A2,A3,A4,B1,B2,B3=sp.symbols('A1 A2 A3 A4 B1 B2 B3')
sol=pickle.load(open('Qsol.pkl','rb'))
a1=t-f-j2-j3;a2=t-f-l2-l3;a3=t-l1-j2-l3;a4=t-l1-l2-j3
b1=f+j2+l1+l2-t;b2=j2+j3+l2+l3-t;b3=j3+f+l3+l1-t
eqs=[A1-a1,A2-a2,A3-a3,A4-a4,B1-b1,B2-b2,B3-b3]
S=sp.solve(eqs,[t,f,j2,j3,l1,l2,l3],dict=True)
print(S)
S=S[0]
J=lambda x:x*(x+1)
D=(J(j3)+J(j2)-J(f))*(J(l3)+J(l2)-J(f))-2*(J(j3)*J(l3)+J(j2)*J(l2)-J(f)*J(l1))
rp=(f+1+j2-j3)*(f+1-j2+j3)*(f+1+l2-l3)*(f+1-l2+l3)
rm=(j2+j3+1-f)*(j2+j3+1+f)*(l2+l3+1-f)*(l2+l3+1+f)
Q6=lambda T: sol[2]*T**2+sol[1]*T+sol[0]
parts=[(2*f+1)*D*(a1+1)*(a2+1)*(b1+1)*(b3+1), f*rp*a1*(a1+1)*a2*(a2+1), (f+1)*rm*b1*(b1+1)*b3*(b3+1), (t+2)*Q6(t+1)*b2*(b1+1)*(b3+1), a3*a4*Q6(t)*(a1+1)*(a2+1)]
vs=(A1,A2,A3,A4,B1,B2,B3)
print([len(sp.Poly(sp.expand(p.subs(S)),*vs).terms()) for p in parts])
