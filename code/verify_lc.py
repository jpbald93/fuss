# sympy checks of the hand-derived linear_combination certificates
from sympy import *
R,r,d2,c,V2,W,X,Y=symbols('R r d2 c V2 W X Y')
k=R**2-d2; s=r**2+c
Z=k**2*c+2*r**2*k*(X+Y)+4*r**4*d2
F=k**2-2*r**2*(R**2+d2)
goal=k*s**2*((V2-2*W+d2)-R**2) - s*(-Z-r**2*F)
h1=s**2*V2-2*r**4*s; h2=s*W-r**2*(X+Y)
print('Forward.vertex_rel key', expand(goal-(k*h1-2*k*s*h2)))
p,q,s_,e=symbols('p q s e')
hs=s_**2-(p-r**2); hq=p*q-1
print('Steps.first_tangent norm', expand((r**2*q)**2*p+(r*s_*q)**2*p-r**2-((p*q**2*r**2)*hs+(p*q*r**2+r**2)*hq)))
print('Steps.first_tangent inner', expand((r**2*q)*p-r**2-r**2*hq))
cc=2*r**2*q
print('Steps.other_tangent norm', expand(cc**2*p-2*(cc*r**2)+r**2-r**2-4*r**4*q*hq))
print('Steps.other_tangent inner', expand(cc*p-r**2-r**2-2*r**2*hq))
E=r**2-(cc*r**2-r**2)
print('Steps.other_tangent ne', expand(r**2*(p-r**2)-((p/2)*E+r**4*hq)))
Rr,dd=symbols('Rr dd')
lhs=((Rr+dd)**2+(Rr-dd)**2)*r**2; rhs=(Rr-dd)**2*(Rr+dd)**2
print('Geometry.fuss_iff_reciprocal', expand((lhs-rhs)+((Rr**2-dd**2)**2-2*r**2*(Rr**2+dd**2))))
