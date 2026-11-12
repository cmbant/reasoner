import pickle,sympy as sp, time
t,f,j2,j3,l1,l2,l3=sp.symbols('t f j2 j3 l1 l2 l3')
def args(F):
    a=[t-F-j2-j3, t-F-l2-l3, t-l1-j2-l3, t-l1-l2-j3]
    b=[F+j2+l1+l2-t, j2+j3+l2+l3-t, j3+F+l3+l1-t]
    return a,b
a0,b0=args(f)
aref=[x+1 for x in a0]; bref=[b0[0]+1,b0[1],b0[2]+1]
def pm(x,r):
    k=int(sp.simplify(r-x)); m=1
    for i in range(1,k+1): m*=(x+i)
    return m
def mult(F):
    a,b=args(F); m=1
    for x,r in zip(a,aref): m*=pm(x,r)
    for x,r in zip(b,bref): m*=pm(x,r)
    return m
a,b=args(f)
eas=[0,0,0,0]; ebs=[1,0,1]
def Hm(shift):
    m=1
    for x,e,r in zip(a,eas,aref): m*=pm(x+shift+e,r)
    for x,e,r in zip(b,ebs,bref): m*=pm(x-shift+e,r)
    return m
print("m0",sp.factor(mult(f)));print("m+",sp.factor(mult(f+1)));print("m-",sp.factor(mult(f-1)))
print("Ho",sp.factor(Hm(0)));print("Hn",sp.factor(Hm(1)))
