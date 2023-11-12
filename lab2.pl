%indata i format ([Premiss],Slutsats,[[radnr,sats,regel]]).
%goal 1 test([p],p,[[1,p,premiss]]).
%goal 2, OR elimination verify(and(a,b),b,).

verify(InputFileName) :- see(InputFileName), read(Prems), read(Goal), read(Proof), seen, valid_proof(Prems, Goal, Proof).

%validproof([Prem|Rest],Goal,[[,X,premise]|Next]):- member(X,Prems), valid_proof(Rest,Goal, Next). %check if premise is in prems
%valid_proof(Prems, Goal, [[Proof]|[]]):- nth0(1,last(Proof,Goal),Goal). %check if last element in proof is goal
getLast([Last|[]],A):-A=Last.
getLast([_|Tail], A):-getLast(Tail,A).

valid_proof(Prems,Goal,Proof):-getLast(Proof,Last),!,nth0(1,Last,Goal),validproof(Prems,Proof,[]).
%Base Case
validproof(_, [], _).
validproof(Prems, [Head|_],List):-validproof(Prems, Head, List).
validproof(Prems,[[_,X,premise]|Tail],List):-member(X,Prems),append(List,[_,X,premise],NewList),validproof(Prems,Tail,NewList).

%ANDEL1
validproof(_,[_,X,andel1(Num)],[Num, Y, _]):-andel1_valid(Num,X,Y).
andel1_valid(_, X, Y):-and(X,_)=Y.

%ANDEL2
validproof(_,[_,X,andel2(Num)],[Num, Y, _]):-andel2_valid(Num,X,Y).
andel2_valid(_, X, Y):-and(_,X)=Y.