import sympy as sp, itertools, sys
t=sp.symbols('t')
R=sp.Rational
f,j2,j3,l1,l2,l3=R(7,2),R(5,3),R(11,5),R(3,7),R(13,4),R(2,9)
def args(F):
    a=[t-F-j2-j3, t-F-l2-l3, t-l1-j2-l3, t-l1-l2-j3]
    b=[F+j2+l1+l2-t, j2+j3+l2+l3-t, j3+F+l3+l1-t]
    return a,b
REF=4
def poly_mult(x,xref):
    # ifa(x)= (x+1)...(x+k) ifa(x+k), k = xref - x (integer>=0)
    k=int(sp.simplify(xref-x)); assert k>=0,(x,xref)
    m=1
    for i in range(1,k+1): m*=(x+i)
    return m
a0,b0=args(f)
aref=[x+REF for x in a0]; bref=[x+REF for x in b0]
def mult(F):
    a,b=args(F)
    m=1
    for x,r in zip(a,aref): m*=poly_mult(x,r)
    for x,r in zip(b,bref): m*=poly_mult(x,r)
    return m
J=lambda x:x*(x+1)
D=(J(j3)+J(j2)-J(f))*(J(l3)+J(l2)-J(f))-2*(J(j3)*J(l3)+J(j2)*J(l2)-J(f)*J(l1))
rp=(f+1+j2-j3)*(f+1-j2+j3)*(f+1+l2-l3)*(f+1-l2+l3)
rm=(j2+j3+1-f)*(j2+j3+1+f)*(l2+l3+1-f)*(l2+l3+1+f)
lhs=sp.expand((2*f+1)*D*mult(f)-f*rp*mult(f+1)-(f+1)*rm*mult(f-1))
def Hmult(h,eas,ebs,shift):
    # H at t+shift: (-1)^(t+shift) (t+shift+1)! h(t+shift) prod ifa(a_i(t+shift)+ea) prod ifa(b_j(t+shift)+eb)
    a,b=args(f)
    m=h.subs(t,t+shift)
    for x,e,r in zip(a,eas,aref): m*=poly_mult((x+shift+e),r)
    for x,e,r in zip(b,ebs,bref): m*=poly_mult((x-shift+e),r)
    # (-1)^shift and (t+shift+1)!/(t+1)! factor
    sign=(-1)**shift
    fac=1
    for i in range(1,shift+1): fac*=(t+1+i)
    return sign*fac*m
d=int(sys.argv[1]) if len(sys.argv)>1 else 7
cs=sp.symbols('c0:%d'%(d+1)); h=sum(c*t**i for i,c in enumerate(cs))
for eaf,ean,ebf,ebn in itertools.product([-1,0,1,2],repeat=4):
    eas=[eaf,eaf,ean,ean]; ebs=[ebf,ebn,ebf]
    ebs=[ebf,ebn,ebf]
    # keep ranges valid: shift+e must be <= ref
    try:
        expr=sp.expand(lhs-(Hmult(h,eas,ebs,1)-Hmult(h,eas,ebs,0)))
    except AssertionError:
        continue
    eqs=sp.Poly(expr,t).all_coeffs()
    sol=sp.solve(eqs,cs,dict=True)
    if sol:
        print("FOUND",eaf,ean,ebf,ebn,sp.factor(h.subs(sol[0]))); sys.stdout.flush()
print("done")
