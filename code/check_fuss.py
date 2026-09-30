# Numerical check of Fuss's theorem / Poncelet 4-closure, incl. negative control.
import math, random
def tangent_pts(a, I, r):
    # tangent points on circle (I,r) from exterior point a
    ux, uy = a[0]-I[0], a[1]-I[1]; p = ux*ux+uy*uy; s = math.sqrt(p-r*r)
    vx, vy = -uy, ux
    return [(I[0]+r*r/p*ux+sg*r*s/p*vx, I[1]+r*r/p*uy+sg*r*s/p*vy) for sg in (1,-1)]
def second_inter(a, T, O, R):
    # line through a and T, other intersection with circle (O,R)
    wx, wy = T[0]-a[0], T[1]-a[1]
    lam = -2*((a[0]-O[0])*wx+(a[1]-O[1])*wy)/(wx*wx+wy*wy)
    return (a[0]+lam*wx, a[1]+lam*wy)
def dline(P, Q, I):
    # distance from I to line PQ
    wx, wy = Q[0]-P[0], Q[1]-P[1]
    return abs(wx*(I[1]-P[1])-wy*(I[0]-P[0]))/math.hypot(wx, wy)
def other_tangent(B, prevT, I, r):
    ts = tangent_pts(B, I, r)
    return max(ts, key=lambda T: math.dist(T, prevT))
def run(R, d, r, th):
    O=(0.0,0.0); I=(d,0.0)
    A=(R*math.cos(th), R*math.sin(th))
    T1,T4 = tangent_pts(A,I,r)
    B = second_inter(A,T1,O,R); D = second_inter(A,T4,O,R)
    T2 = other_tangent(B,T1,I,r); T3 = other_tangent(D,T4,I,r)
    C = second_inter(B,T2,O,R); C2 = second_inter(D,T3,O,R)
    return math.dist(C,C2), dline(C,D,I)-r
random.seed(1); worst=0
for _ in range(2000):
    R=random.uniform(1,5); d=random.uniform(0,0.9)*R; k=R*R-d*d
    r=k/math.sqrt(2*(R*R+d*d))
    assert r < R-d
    e1,e2=run(R,d,r,random.uniform(0,2*math.pi)); worst=max(worst,abs(e1),abs(e2))
print("Fuss holds: max closure error", worst)
bad=min(abs(run(3,1,r0,0.7)[0]) for r0 in [0.9*(8/math.sqrt(20)), 1.1*(8/math.sqrt(20))])
print("negative control (r off by 10%): closure gap", bad)
# key identity: G(x,y) = -k<x-Q0,y-Q0> - (r^2/k) F
for _ in range(100):
    R=random.uniform(1,5); d=random.uniform(0,.9)*R; r=random.uniform(.1,1); k=R*R-d*d
    o=(random.gauss(0,1),random.gauss(0,1)); nrm=math.hypot(*o); o=(o[0]*d/nrm,o[1]*d/nrm)
    x=(random.gauss(0,1),random.gauss(0,1)); y=(random.gauss(0,1),random.gauss(0,1))
    dot=lambda u,v:u[0]*v[0]+u[1]*v[1]
    G=2*r**4-2*r*r*(dot(o,x)+dot(o,y))-k*(r*r+dot(x,y))
    Q=(-2*r*r/k*o[0],-2*r*r/k*o[1]); F=k*k-2*r*r*k-4*r*r*d*d
    assert abs(G-(-k*dot((x[0]-Q[0],x[1]-Q[1]),(y[0]-Q[0],y[1]-Q[1]))-r*r/k*F))<1e-8
print("shift identity ok; example R=7,d=1,r=24/5:", (49-1)**2, 2*(24/5)**2*(50))

# --- general (non-convex / any position) check via tangency-point parametrisation ---
# vertex between tangency points x,y of omega (I=0): V = r^2 (x+y)/(r^2+<x,y>)
import cmath
def V(x,y,r):
    c=x[0]*y[0]+x[1]*y[1]; return (r*r*(x[0]+y[0])/(r*r+c), r*r*(x[1]+y[1])/(r*r+c))
def circ(P1,P2,P3):
    ax,ay=P1;bx,by=P2;cx,cy=P3
    D=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
    ux=((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/D
    uy=((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/D
    return (ux,uy), math.dist((ux,uy),P1)
# random 3 tangency pts define A,B,C; circumcircle Gamma; then solve for 4th tangency pt x4 with D=V(x3,x4) and A=V(x4,x1) on Gamma
random.seed(7); cnt=0; worst=0
for _ in range(300):
    r=1.0; th=[random.uniform(0,2*math.pi) for _ in range(3)]
    x=[(math.cos(t),math.sin(t)) for t in th]
    try:
        A=V(x[0],x[1],r); B=V(x[1],x[2],r)  # A between x0,x1 ; B between x1,x2
    except ZeroDivisionError: continue
    # need a third vertex: pick x3 by scanning so that C=V(x2,x3) and D=V(x3,x0)?? (quadrilateral x0..x3)
    # scan x3 angle: vertices A,B,C=V(x2,x3),D=V(x3,x0); concyclic condition
    def f(t):
        try:
            x3=(math.cos(t),math.sin(t)); C=V(x[2],x3,r); D=V(x3,x[0],r)
            O,Rr=circ(A,B,C); return math.dist(O,D)-Rr, O, Rr
        except ZeroDivisionError:
            return float('nan'),None,None
    ts=[i*2*math.pi/4000 for i in range(4001)]
    prev=None
    for t in ts:
        v=f(t)[0]
        if v!=v: prev=None; continue
        if prev is not None and prev[1]*v<0 and abs(v)<1 and abs(prev[1])<1:
            lo,hi=prev[0],t
            for _ in range(60):
                mid=(lo+hi)/2
                if f(lo)[0]*f(mid)[0]<=0: hi=mid
                else: lo=mid
            val,O,Rr=f(lo)
            if O is not None and abs(val)<1e-9:
                d2=O[0]**2+O[1]**2; k=Rr*Rr-d2
                x3=(math.cos(lo),math.sin(lo))
                if min(math.dist(x3,xx) for xx in x)>1e-3 and abs(k)>1e-3:
                    worst=max(worst,abs(k*k-2*r*r*(Rr*Rr+d2))/(k*k)); cnt+=1
        prev=(t,v)
print("general tangency configs found:",cnt,"max rel Fuss defect:",worst)
# k=0 counterexample (I on Gamma): Fuss fails
Rr=2.0; r=0.5; d=Rr; o=(d,0)
a=0.3; c=r/d*r - a  # need <o,x_i+x_{i+1}> = r^2 with x=(r*cos,...): d*r*(ca+cc)=r^2
ca=0.3; cc=r/d-ca
xs=[(r*ca,r*math.sqrt(1-ca*ca)),(r*cc,r*math.sqrt(1-cc*cc)),(r*ca,-r*math.sqrt(1-ca*ca)),(r*cc,-r*math.sqrt(1-cc*cc))]
Vs=[V(xs[i],xs[(i+1)%4],r) for i in range(4)]
print("k=0 example: dist of vertices to O:",[round(math.dist(P,o),12) for P in Vs],"Fuss lhs,rhs:",0,2*r*r*(Rr*Rr+d*d))
print("k=0 example vertices (distinct):", [tuple(round(c,4) for c in P) for P in Vs])
