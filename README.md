# sim_onetomany  
# my .pv file
type element. (*element in finite field or group*) (*定义一个环境*)
free Sec:channel [private].		(*secure channel*)
free Pub:channel.			(*public channel*)


(*-------Names & Variables-------*)
(*elements of cyclic group*)
const g:element.  (*生成元*)

(*1. KGC public key*)
free Ppub:element.

(*2 . KGC master secret key*)


(*1. RSUs' private key*)
(*RSUj*)
free U:element [private].
free a0:element [private].
free a1:element [private].
free a2:element [private].
free a3:element [private].
free a4:element [private].
free a5:element [private].

(*2. RSUs' public parameters*)
(*RSUj*)
free Q0:element.
free Q1:element.
free Q2:element.
free Q3:element.
free Q4:element.
free Q5:element.
free W:element.
free IDj:bitstring.
free Yj:element. (*vector Y*)
free y1j:element.
free y2j:element.
free y3j:element.
free y4j:element.
free y5j:element.


(*5. Vehicles' private key*)
(*Vi*)
free K0i:element [private].
free K1i:element [private].
free S2:element [private].
free S3:element [private].
free S4:element [private].
free S5:element [private].


(*6. Vehicles' public parameters*)
(*Vi*)
free PIDi:bitstring.
free Xi:element. (*vector X*)
free x1i:element.
free x2i:element.
free x3i:element.
free x4i:element.
free x5i:element.

(*vehicle i & identity*)
free IDi:bitstring.

(*7. session key*)
free K:element [private].
free K':element [private].

(*8. else Parameters*)
free M:element [private].
free M':element [private].


(*-------Constructors, Destructors & Equations------*)
fun Xor(bitstring,bitstring):bitstring.
fun H(bitstring,bitstring,element):element.
fun H0(element,element):bitstring.
fun H1(element,element,element,element,element,element,element,element,element,bitstring,element):element.
fun inv(element):element. (*inverse*)
fun neg(element):element. (*negation*)
fun con(element,element,element,element,element):element. (*concatenation operator*)
fun Pairing(element,element):element.  (*Pairing operation:e(g,g)*)
fun Mult(element,element):element.  (*Multiplication in group: G×G*)
fun Add(element,element):element.	 (*Addition*)
fun Powzn(element,element):element. 	(*g^s:Powzn(g,s)*)

(*Event*)
event beginRSUj(bitstring).
event endRSUj(bitstring).
event beginVehiclei(bitstring).
event endVehiclei(bitstring).

(*Queries*)
query attacker(K).(*通过这些询问验证会话密钥的安全性*)
query attacker(K').
query ID:bitstring; inj-event (endRSUj(IDj)) ==> inj-event(beginRSUj(IDj)). (*签名的不可伪造性*)
query ID:bitstring; inj-event (endVehiclei(IDi)) ==> inj-event(beginVehiclei(IDi)).
(*Processes*)
(*KGC Processes*)
let RSUjReg=
	in(Sec,(IDj:bitstring)); 
	new s:element;
	let U = Powzn(g,s) in 
	let Q0=Powzn(g,a0) in 
	let Q1=Powzn(g,a1) in 
	let Q2=Powzn(g,a2) in 
	let Q3=Powzn(g,a3) in 
	let Q4=Powzn(g,a4) in 
	let Q5=Powzn(g,a5) in 
	let W=Powzn(Pairing(g,g),s) in
	0.
let KGC=RSUjReg.
(*RSUj Processes*)
let VehicleiReg=
	in(Sec,(IDi:bitstring,Xi:element)); (*in：输入*)
	new zi:element;
	let Zi = Powzn(g,zi) in        (*每个运算let开始 in结束*)
	let PIDi=Xor(H0(a0,Zi),IDi) in
	let K0i=H(IDj,PIDi,Xi) in
	let K1i=Mult(U,Powzn(H(IDj,PIDi,Xi),a0)) in
	let temp2=Add(a2,Mult(neg(a1),Mult(x2i,inv(x1i)))) in
	let temp3=Add(a3,Mult(neg(a1),Mult(x3i,inv(x1i)))) in
	let temp4=Add(a4,Mult(neg(a1),Mult(x4i,inv(x1i)))) in
	let temp5=Add(a5,Mult(neg(a1),Mult(x5i,inv(x1i)))) in
	let S2=Powzn(H(IDj,PIDi,Xi),temp2) in
	let S3=Powzn(H(IDj,PIDi,Xi),temp3) in
	let S4=Powzn(H(IDj,PIDi,Xi),temp4) in
	let S5=Powzn(H(IDj,PIDi,Xi),temp5) in
	0.

let RSUj=
	(*Registration*)
	out(Sec,IDj);
	
	(*RSU&Vehicles Authentication*)
	event beginRSUj(IDj);
	new t1:element;
	new r:element;
	new T1:element;
	new C0:element;
	new C1:element;
	new C2:element;
	let Yj=con(y1j,y2j,y3j,y4j,y5j) in
	let T1 = Powzn(g,t1) in 
	let C0 = Mult(M,Powzn(W,r)) in
	let C1 = Powzn(Mult(Mult(Mult(Mult(Mult(Q0,Powzn(Q1,y1j)),Powzn(Q2,y2j)),Powzn(Q3,y3j)),Powzn(Q4,y4j)),Powzn(Q5,y5j)),r) in
	let C2 = Powzn(g,r) in 
	new sigma:element;
	new Gamma1:element;
	new alpha:element;
	let sigma = Add(t1,Mult(a0,H1(T1,M,Q0,Q1,Q2,Q3,Q4,Q5,W,IDj,Gamma1))) in
	let P1 = Powzn(g,alpha) in 
	out(Sec,(C0,C1,C2,sigma,P1,T1,Gamma1));
	
	in(Sec,(P2:element,Gamma2:element));
	
	let K' = Powzn(P2,alpha) in
	event endRSUj(IDj)
	else 0.


(*Vehicle Processes*)
(*Vi Processes*)
let Vehiclei=
	(*Registration*)
	let Xi = con(x1i,x2i,x3i,x4i,x5i) in 
	out(Sec,(IDi,Xi));
	
	(*RSU&Vehicles Authentication*)
	
    event beginVehiclei(IDi);
	in(Sec,(C0:element,C1:element,C2:element,sigma:element,P1:element,T1:element,Gamma1:element));
	let R1=Pairing(Mult(Mult(Mult(Mult(K1i,Powzn(S2,y2j)),Powzn(S3,y3j)),Powzn(S4,y4j)),Powzn(S5,y5j)),C2) in
	let R2=Pairing(C1,K0i) in
	let Ri=Mult(R1,inv(R2)) in
	let M'=Mult(C0,inv(Ri)) in
	if(Powzn(g,sigma)= Add(T1,Mult(H1(T1,M',Q0,Q1,Q2,Q3,Q4,Q5,W,IDj,Gamma1),Q0))) then
	
	new beta:element;
	new P2:element;
	new Gamma2:element;
	let P2=Powzn(g,beta) in
	let K= Powzn(g,beta) in
    out(Sec,(P2,Gamma2));
	
	event endVehiclei(IDi)
    else 0.
	(*Processes Replication*)
	process 
    (!RSUj | !Vehiclei | !KGC)
