
import numpy as np
import z3

solver = z3.Solver()

inputalphabet = {"a","b","c"}
outputalphabet = {"A","B"}
domain = {"","a","b","c","ac","bc","acc","bcc"}

Table_sharp = {}
Table_bot = {}
Table = {}

Table_sharp[""] = False
Table_bot[""] = True
Table[""] = ""

Table_sharp["a"] = False
Table_bot["a"] = False
Table["a"] = ""

Table_sharp["b"] = False
Table_bot["b"] = True
Table["b"] = ""

Table_sharp["c"] = False
Table_bot["c"] = True
Table["c"] = ""

Table_sharp["ac"] = True
Table_bot["ac"] = False
Table["ac"]= ""

Table_sharp["bc"] = False
Table_bot["bc"] = False
Table["bc"] = "1"


Table_sharp["acc"] = True
Table_bot["acc"] = False
Table["acc"] = ""

Table_sharp["bcc"] = True
Table_bot["bcc"] = False
Table["bcc"] = ""


E = {}
for element1 in domain:
	E[element1] = {}
	for element2 in domain:
		E[element1][element2] = z3.Bool("E_"+element1+"_"+element2)
			#Better E[element1][element2] or E[element1[element2]] in python?
		
bound = 3
	
f = {}
f_bot = {}
f_char = {}
for element in domain:
	f_char[element] = []
	f[element] = z3.String("f_"+element)
	f_bot[element] = z3.Bool("f_"+element+"_bot")
	for index in range(bound):
		f_char[element].append(z3.String("f_char_"+element+"_"+str(index)))
	
u = z3.String("u")


n = 4 #Size of the word recognized here. This is temporary

bound_w = 3


# Accepted word

delta = {}
for word in domain:
	delta[word] = {}
	for letter in inputalphabet:
		delta[word][letter] = z3.String("delta_"+word+"_"+letter)

v = {}
v_bot = {}
w = {}
w_bot = {}
for index in range(n+1):
	v[index] = z3.String("v_"+str(index))
	v_bot[index] = z3.Bool("v_"+str(index)+"_bot")
for index in range(n):
	w[index] = z3.String("w_"+str(index))
	w_bot[index] = z3.Bool("w_"+str(index)+"_bot")
w_out = z3.String("w_out")

w_char = {}
for index1 in range(n):
	w_char[index1] = []
	for index2 in range(bound_w):
		w_char[index1].append(z3.String("w_char"+str(index1)+"_"+str(index2)))
	



################ Def outputvalues

outvalues = []
conj = {}
disj = {}
for element in domain:
	conj[element] = []
	disj[element] = {}
	for index in range(bound):
		disj[element][index] = []
		disj[element][index].append(z3.PrefixOf(f_char[element][index],""))
		for letter in outputalphabet:
			disj[element][index].append(z3.And(
			z3.PrefixOf(f_char[element][index],letter),
			z3.PrefixOf(letter,f_char[element][index])))
		if index > 0:
			conj[element].append(z3.Implies(
			z3.PrefixOf(f_char[element][index-1],""),
			z3.PrefixOf(f_char[element][index],"")))
		conj[element].append(z3.And(
		z3.SubSeq(f[element],index,1) == f_char[element][index],
		z3.Or(disj[element][index])))
	outvalues.append(z3.And(conj[element]))



conj = {}
disj = {}
for index1 in range(n):
	conj[index1] = []
	disj[index1] = {}
	for index2 in range(bound_w):
		disj[index1][index2] = []
		disj[index1][index2].append(z3.PrefixOf(w_char[index1][index2],""))
		for letter in outputalphabet:
			disj[index1][index2].append(z3.And(
			z3.PrefixOf(w_char[index1][index2],letter),
			z3.PrefixOf(letter,w_char[index1][index2])))
		if index2 > 0:
			conj[index1].append(z3.Implies(
			z3.PrefixOf(w_char[index1][index2-1],""),
			z3.PrefixOf(w_char[index1][index2],"")))
		conj[index1].append(z3.And(
		z3.SubSeq(w[index1],index2,1) == w_char[index1][index2],
		z3.Or(disj[index1][index2])))
	outvalues.append(z3.And(conj[index1]))

#		disj.append(z3.Or(z3.Contains(letter,z3.SubSeq(f[element],i_value,1))))
#	outvalues.append(
#	z3.And(
#	(z3.Length(f[element]) == f_length[element]), ( z3.Length(f[element]) < bound),
#	z3.ForAll([i_value],z3.Implies(z3.And((i_value < f_length[element]),(i_value >= 0)),z3.And(disj)))
#	))


################ Def equivalence

def_eq = []

eq_1 = []
for element1 in domain:
	eq_1.append(E[element1][element1])

def_eq.append(z3.And(eq_1))
		
	
eq_2 = []
for element1 in domain:
	for element2 in domain:
		eq_2.append(
		E[element1][element2] == E[element2][element1]
		)
		
def_eq.append(z3.And(eq_2))

	
eq_3 = []
for element1 in domain:
	for element2 in domain:
		for element3 in domain:
			eq_3.append(
			z3.Implies(
			z3.And(
			E[element1][element2]
			,
			E[element2][element3]
			)
			,
			E[element1][element3]
			)
			)
		

def_eq.append(z3.And(eq_3))

solver.add(def_eq)
		
################## lemma 20


def_20 = []

eq20_1 = []
for element1 in domain:
	for element2 in domain:
		eq20_1.append(
		z3.And(
		z3.Implies(f_bot[element1],
		z3.Implies(f_bot[element2],E[element1][element2]
		)),
		z3.Implies(f_bot[element1], 
		z3.Implies(E[element1][element2],f_bot[element2]
		))
		)
		)


def_20.append(z3.And(eq20_1))




	
eq20_2 = []
for element1 in domain:
	for element2 in domain:
		if element1+element2 in domain :
			eq20_2.append(z3.Implies( 
			 z3.And(
				z3.Not(Table_bot[element1+element2]),
				z3.Not(Table_sharp[element1+element2])
				)
			,
			 z3.And(
				z3.Not(f_bot[element1]),
				z3.PrefixOf(f[element1],
				f[element1+element2])
				)
			)
			)
				
def_20.append(z3.And(eq20_2))


eq20_3 = []
for element in domain:
	for letter in inputalphabet:
		if element+letter in domain:
			eq20_3.append(
			z3.Implies( 
			z3.Not(f_bot[element+letter]),
			z3.And(z3.Not(f_bot[element]),
			z3.PrefixOf(f[element],f[element+letter])
			)
			))
			

def_20.append(z3.And(eq20_3))


eq20_4 = []
for element1 in domain:
	for element2 in domain:
		for letter in inputalphabet:
			if (element1+letter in domain) and (element2+letter in domain):
				eq20_4.append
				(
				z3.Implies
				(z3.And(z3.Not(f_bot[element1]),E[element1][element2]),
				z3.And(
				E[element1+letter][element2+letter],
				z3.Implies(z3.Not(f_bot[element1+letter]),
				z3.And(
				z3.PrefixOf(f[element1],
				f[element1+letter]),
				z3.PrefixOf(f[element2],
				f[element2+letter]), 
				z3.SubSeq(f[element1+letter],1+z3.Length(f[element1]),
				z3.Length(f[element1+letter])-z3.Length(f[element1])) 
				==
				z3.SubSeq(f[element2+letter],1+z3.Length(f[element2]),
				z3.Length(f[element2+letter])-z3.Length(f[element2]))
				)))))


def_20.append(z3.And(eq20_4))


eq20_5 = []
for element1 in domain:
	for element2 in domain:
		eq20_5.append(
			z3.Implies(
			z3.And
			(z3.Not(Table_bot[element1]),z3.Not(Table_sharp[element1]),
			z3.Not(Table_sharp[element2]),E[element1][element2]
			),
			z3.SubSeq(Table[element1],1+z3.Length(f[element1]),
			z3.Length(Table[element1])-z3.Length(f[element1]))
			==
			z3.SubSeq(Table[element2],1+z3.Length(f[element2]),
			z3.Length(Table[element2])-z3.Length(f[element2]))
			)
			)

def_20.append(z3.And(eq20_5))


eq20_6 = []
conj = {}
for element1 in domain:
	for letter in inputalphabet:
		if element1+letter in domain:
			conj[element1+letter] = []
			for element2 in domain:
				if element2+letter in domain:
					conj[element1+letter].append(z3.Not(E[element1][element2]))
			if conj[element1+letter] != []:
				eq20_6.append(
				z3.Implies( 
				z3.And(
				z3.Not(f_bot[element1+letter]),
				z3.And(conj[element1+letter])
				),
				(f[element1] == f[element1+letter])
				))

def_20.append(z3.And(eq20_6))
				

#solver.add(def_20)

################## lemma 21 part 1

def_21 = []


eq21_1 = []
for index in range(0,n):
	eq21_1.append(
		z3.And(
		((z3.Length(u) < index) == w_bot[index])
		)
		)
for index in range(0,n+1):
	eq21_1.append(
		z3.And(
		((z3.Length(u) < index) == v_bot[index])
		)
		)

def_21.append(z3.And(eq21_1))


eq21_2 = []
for index in range(1,n+1):
	for element1 in domain:
		for element2 in domain:
			for letter in inputalphabet:
				if element2+letter in domain:
					eq21_2.append((
					z3.Implies((z3.Length(u) >= index),
					(z3.And(
					z3.And(
					z3.PrefixOf(v[index],element1),
					z3.PrefixOf(element1,v[index])),
					z3.And(
					z3.PrefixOf(v[index-1],element2),
					z3.PrefixOf(element2,v[index-1])),
					z3.And(
					z3.PrefixOf(z3.SubSeq(u,index,1),letter),
					z3.PrefixOf(letter,z3.SubSeq(u,index,1))),
					E[element1][element2+letter])
					)
					)
					))

def_21.append(z3.And(eq21_2))

eq21_3 = z3.And(
z3.PrefixOf(v[0],""),
z3.PrefixOf("",v[0]))

def_21.append(z3.And(eq21_3))

eq21_4 = []
for element in domain:
	for letter in inputalphabet:
		if element+letter in domain:
			eq21_4.append(z3.And(
			(z3.Concat(f[element],delta[element][letter]) == f[element+letter])))
#			z3.PrefixOf(z3.Concat(f[element],delta[element][letter]),f[element+letter]),
#			z3.PrefixOf(f[element+letter],z3.Concat(f[element],delta[element][letter]))))

def_21.append(z3.And(eq21_4))


eq21_5 = []
disj = {}
for index in range(1,n):
	disj[index] = []
	for element1 in domain:
		for element2 in domain:
			for letter in inputalphabet:
				if element2+letter in domain:
					disj[index].append(
					z3.And(
					z3.And(
					z3.PrefixOf(w[index],element1),
					z3.PrefixOf(element1,w[index])),
					z3.And(
					z3.PrefixOf(v[index-1],element2),
					z3.PrefixOf(element2,v[index-1])),
					z3.And(
					z3.PrefixOf(z3.SubSeq(u,index,1),letter),
					z3.PrefixOf(letter,z3.SubSeq(u,index,1))),
					z3.And(
					(w[index] == delta[element2][letter]))
#					z3.PrefixOf(w[index],delta[element2][letter]),
#					z3.PrefixOf(delta[element2][letter],w[index]))
					)
					)
	eq21_5.append(z3.And(
	z3.Implies(
	(z3.Length(u) >= index),
	z3.Or(disj[index])
	)))



def_21.append(z3.And(eq21_5))
	
eq21_6 = []
for element1 in domain:
	for index in range(n+1):
		eq21_6.append(
		z3.Or( z3.Implies( 
		z3.And(
		z3.PrefixOf(v[index],element1),
		z3.PrefixOf(element1,v[index])),
		z3.And(
		z3.PrefixOf(z3.Concat(f[element1],w_out),Table[element1]),
		z3.PrefixOf(Table[element1],z3.Concat(f[element1],w_out)))
		)))



def_21.append(z3.And(eq21_6))

################## Second word

# Rejected word


v2 = {}
v2_bot = {}
w2 = {}
w2_bot = {}
for index in range(n+1):
	v2[index] = z3.String("v2_"+str(index))
	v2_bot[index] = z3.Bool("v2_"+str(index)+"_bot")
for index in range(n):
	w2[index] = z3.String("w2_"+str(index))
	w2_bot[index] = z3.Bool("w2_"+str(index)+"_bot")
w2_out = z3.String("w2_out")

w2_char = {}
for index1 in range(n):
	w2_char[index1] = []
	for index2 in range(bound_w):
		w2_char[index1].append(z3.String("w2_char"+str(index1)+"_"+str(index2)))
	

delta2={}
for word in domain:
	delta2[word] = {}
	for letter in inputalphabet:
		delta2[word][letter] = z3.String("delta2_"+word+"_"+letter)




################ Def outputvalues
	
f2 = {}
f2_bot = {}
f2_char = {}
for element in domain:
	f2_char[element] = []
	f2[element] = z3.String("f2_"+element)
	f2_bot[element] = z3.Bool("f2_"+element+"_bot")
	for index in range(bound):
		f2_char[element].append(z3.String("f2_char_"+element+"_"+str(index)))
	


conj = {}
disj = {}
for element in domain:
	conj[element] = []
	disj[element] = {}
	for index in range(bound):
		disj[element][index] = []
		disj[element][index].append(z3.PrefixOf(f2_char[element][index],""))
		for letter in outputalphabet:
			disj[element][index].append(z3.And(
			z3.PrefixOf(f2_char[element][index],letter),
			z3.PrefixOf(letter,f2_char[element][index])))
		if index > 0:
			conj[element].append(z3.Implies(
			z3.PrefixOf(f2_char[element][index-1],""),
			z3.PrefixOf(f2_char[element][index],"")))
		conj[element].append(z3.And(
		z3.SubSeq(f2[element],index,1) == f2_char[element][index],
		z3.Or(disj[element][index])))
	outvalues.append(z3.And(conj[element]))



conj = {}
disj = {}
for index1 in range(n):
	conj[index1] = []
	disj[index1] = {}
	for index2 in range(bound_w):
		disj[index1][index2] = []
		disj[index1][index2].append(z3.PrefixOf(w2_char[index1][index2],""))
		for letter in outputalphabet:
			disj[index1][index2].append(z3.And(
			z3.PrefixOf(w2_char[index1][index2],letter),
			z3.PrefixOf(letter,w2_char[index1][index2])))
		if index2 > 0:
			conj[index1].append(z3.Implies(
			z3.PrefixOf(w2_char[index1][index2-1],""),
			z3.PrefixOf(w2_char[index1][index2],"")))
		conj[index1].append(z3.And(
		z3.SubSeq(w2[index1],index2,1) == w2_char[index1][index2],
		z3.Or(disj[index1][index2])))
	outvalues.append(z3.And(conj[index1]))

#		disj.append(z3.Or(z3.Contains(letter,z3.SubSeq(f[element],i_value,1))))
#	outvalues.append(
#	z3.And(
#	(z3.Length(f[element]) == f_length[element]), ( z3.Length(f[element]) < bound),
#	z3.ForAll([i_value],z3.Implies(z3.And((i_value < f_length[element]),(i_value >= 0)),z3.And(disj)))
#	))


		
################## lemma 20


def_20b = []

eq20b_1 = []
for element1 in domain:
	for element2 in domain:
		eq20b_1.append(
		z3.And(
		z3.Implies(f2_bot[element1],
		z3.Implies(f2_bot[element2],E[element1][element2]
		)),
		z3.Implies(f2_bot[element1], 
		z3.Implies(E[element1][element2],f2_bot[element2]
		))
		)
		)


def_20b.append(z3.And(eq20b_1))




	
eq20b_2 = []
for element1 in domain:
	for element2 in domain:
		if element1+element2 in domain :
			eq20b_2.append(z3.Implies( 
			 z3.And(
				z3.Not(Table_bot[element1+element2]),
				z3.Not(Table_sharp[element1+element2])
				)
			,
			 z3.And(
				z3.Not(f2_bot[element1]),
				z3.PrefixOf(f2[element1],
				f2[element1+element2])
				)
			)
			)
				
def_20b.append(z3.And(eq20b_2))


eq20b_3 = []
for element in domain:
	for letter in inputalphabet:
		if element+letter in domain:
			eq20b_3.append(
			z3.Implies( 
			z3.Not(f2_bot[element+letter]),
			z3.And(z3.Not(f2_bot[element]),
			z3.PrefixOf(f2[element],f2[element+letter])
			)
			))
			

def_20b.append(z3.And(eq20b_3))


eq20b_4 = []
for element1 in domain:
	for element2 in domain:
		for letter in inputalphabet:
			if (element1+letter in domain) and (element2+letter in domain):
				eq20b_4.append
				(
				z3.Implies
				(z3.And(z3.Not(f2_bot[element1]),E[element1][element2]),
				z3.And(
				E[element1+letter][element2+letter],
				z3.Implies(z3.Not(f2_bot[element1+letter]),
				z3.And(
				z3.PrefixOf(f2[element1],
				f2[element1+letter]),
				z3.PrefixOf(f2[element2],
				f[element2+letter]), 
				z3.SubSeq(f2[element1+letter],1+z3.Length(f[element1]),
				z3.Length(f2[element1+letter])-z3.Length(f[element1])) 
				==
				z3.SubSeq(f2[element2+letter],1+z3.Length(f2[element2]),
				z3.Length(f2[element2+letter])-z3.Length(f2[element2]))
				)))))


def_20b.append(z3.And(eq20b_4))


eq20b_5 = []
for element1 in domain:
	for element2 in domain:
		eq20b_5.append(
			z3.Implies(
			z3.And
			(z3.Not(Table_bot[element1]),z3.Not(Table_sharp[element1]),
			z3.Not(Table_sharp[element2]),E[element1][element2]
			),
			z3.SubSeq(Table[element1],1+z3.Length(f2[element1]),
			z3.Length(Table[element1])-z3.Length(f2[element1]))
			==
			z3.SubSeq(Table[element2],1+z3.Length(f2[element2]),
			z3.Length(Table[element2])-z3.Length(f2[element2]))
			)
			)

def_20b.append(z3.And(eq20b_5))


eq20b_6 = []
conj = {}
for element1 in domain:
	for letter in inputalphabet:
		if element1+letter in domain:
			conj[element1+letter] = []
			for element2 in domain:
				if element2+letter in domain:
					conj[element1+letter].append(z3.Not(E[element1][element2]))
			if conj[element1+letter] != []:
				eq20b_6.append(
				z3.Implies( 
				z3.And(
				z3.Not(f2_bot[element1+letter]),
				z3.And(conj[element1+letter])
				),
				(f2[element1] == f2[element1+letter])
				))

def_20b.append(z3.And(eq20b_6))
				



################## lemma 21 part 2

def_21b = []


eq21b_1 = []
eq21b_1 = z3.And(
z3.PrefixOf(v2[0],""),
z3.PrefixOf("",v2[0]))

def_21b.append(z3.And(eq21b_1))

eq21b_2 = []
for index in range(1,n+1):
	for element1 in domain:
		for element2 in domain:
			for letter in inputalphabet:
				if element2+letter in domain:
					eq21_2.append(
					z3.Implies(
					z3.And(
					(z3.Length(u) >= index),
					z3.And(
					z3.PrefixOf(v2[index],element1),
					z3.PrefixOf(element1,v2[index]))
					),
					(z3.Or(
					v2_bot[index],
					z3.And(
					z3.PrefixOf(v2[index-1],element2),
					z3.PrefixOf(element2,v2[index-1])),
					z3.And(
					z3.PrefixOf(z3.SubSeq(u,index,1),letter),
					z3.PrefixOf(letter,z3.SubSeq(u,index,1))),
					E[element1][element2+letter])
					)))

def_21b.append(z3.And(eq21b_2))


eq21b_3 = []
conj = []
for element1 in domain:
	for element2 in domain:
		conj.append(
		z3.Implies(
		z3.And(
		z3.PrefixOf(v2[n],element1),
		z3.PrefixOf(element1,v2[n])),
		z3.Implies(E[element1][element2],
		Table_bot[element2]
		)
		))

eq21b_3.append(z3.And(z3.Or(v2_bot[n],z3.And(conj))))

def_21b.append(z3.And(eq21b_3))



formula = []
formula.append(z3.And(outvalues))
formula.append(z3.And(def_eq))
formula.append(z3.And(def_20))
formula.append(z3.And(def_21))
formula.append(z3.And(def_20b))
formula.append(z3.And(def_21b))
print(z3.solve(formula))
