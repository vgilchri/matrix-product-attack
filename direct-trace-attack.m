clear;

// parameters ------------------------------------
//p := 2^(53)+5; n := 4; k := 9; // toy example
//p := 2^(167) + 83; n := 8; k := 21; // challenge
//p := 2^(302) + 307; n := 10; k := 35; // recommended
p := 2^(1105)-1335; n:= 24; k := 99; // large
Fp := FiniteField(p);



// key gen ----------------------------------------

KeyGen := function()
	// generate dwarf set for private key
	dwarves := [];
	while #dwarves lt k do 
		entries := [Fp!Random([0,1,2]) : i in [1..n^2]]; // sample random entries until invertible
		D := Matrix(n,n,entries);
		if Determinant(D) ne 0 and not (D in dwarves) then 
			dwarves cat:= [D];
		end if;
	end while;

	// select secret elf
	E := Matrix(n,n,[0:i in [1..n^2]]);
	while Determinant(E) eq 0 do 
		entries := [Random(Fp) : i in [1..n^2]];
		E := Matrix(n,n,entries);
	end while;
	Einv := E^(-1);

	// compute public key
	elves := [];
	for D in dwarves do 
		T := E * D * Einv;
		elves cat:= [T];
	end for;

	// choose a permutation
	sigma := [];
	while #sigma lt k do 
		x := Random([i : i in [1..k]]);
		if not (x in sigma) then 
			sigma cat:= [x];
		end if;
	end while;

	// compute ciphertext
	C := elves[sigma[1]];
	for j in [2..#sigma] do 
		C *:= elves[sigma[j]];
	end for;
	return dwarves, E, elves, sigma, C;
end function;

// trace attacks -----------------------------------------

Identity := function(Fp,n) // make identity matrix
	M := ZeroMatrix(Fp,n);
	for i in [1..n] do 
		M[i][i] := Fp!1;
	end for;
	return M;
end function;

TraceAttack := function(C,elves)
	I := Identity(Fp,n);
	prods := [I]; // track "good" products, i.e. mult. by inverse decreases trace
	inds := [[]]; // track the index ordering that defines the good products i.e. prod=A1 A2 -> index = [1,2]
	for i in [1..k] do // growing the product one at a time
		prods1 := []; // next set of good products and corresponding index ordering
		inds1 := [];
		for t in [1..#prods] do // for each element in S--our set of "good" products
			for j in [1..k] do // try multiplying by each public key
				if not (j in inds[t]) then // make sure the matrix is not already in the product
					if i eq k then // we deal with the last matrix separately because multiplying by inverse results in identity whose trace may be higher
						newprod := [prods[t] * elves[j]]; // in this case, take whatever matrix is missing (there's only one)
						newinds := [inds[t] cat [j]];
						prods1 cat:= newprod; inds1 cat:= newinds;
					else
					M := elves[j]^(-1) * prods[t]^(-1) * C; // compute new product
					if Trace(M) lt Trace(elves[j]*M) then // check if mult. by inverse leads to decreased trace
						newprod := [prods[t] * elves[j]]; // if it does, keep in new list
						newinds := [inds[t] cat [j]];
						prods1 cat:= newprod; inds1 cat:= newinds;
					end if;
					end if;
				end if;
			end for;
		end for;
		prods := prods1; inds := inds1; // update list to only include newest products
	end for;
	return inds;
end function;


count := 0;
for x in [1..20] do 
	dwarves,E,elves,sigma,C := KeyGen();
	time guesses := TraceAttack(C,elves);
// if #guesses gt 0 then 
// 	if sigma in guesses then 
// 		count +:=1;
// 	end if;
// end if;
end for;
//count;


