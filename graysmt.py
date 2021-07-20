
import numpy as np
import z3

solver = z3.Solver()

inputalphabet = {"a","b","c"}
outputalphabet = {"1","0"}
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
			
f = {}
f_bot = {}
f_length = {}
for element in domain:
	f[element] = z3.String("f_"+element)
	f_length[element] = z3.Int("f_"+element+"_length")
	f_bot[element] = z3.Bool("f_"+element+"_bot")
	
bound = 3
i_value = z3.Int("i")

################ Def outputvalues

outvalues = []
for element in domain:
	disj = []
	for letter in outputalphabet:
		disj.append(z3.Or(z3.Contains(letter,z3.SubSeq(f[element],i_value,1))))
	outvalues.append(
	z3.And(
	(z3.Length(f[element]) == f_length[element]), ( z3.Length(f[element]) < bound),
	z3.ForAll([i_value],z3.Implies(z3.And((i_value < f_length[element]),(i_value >= 0)),z3.And(disj)))
	))


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
				)
				)
				)
				)
				)


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

################## lemma 21

##n = 5 #Size of the word recognized here. This is temporary

##def_21 = []

##v = {}
##v_bot = {}
##w = {}
##w_bot = {}
##for index in range(0,n):
##	v[index] = z3.String("v_"+index)
##	v_bot[index] = z3.Bool("v_"+index+"_bot")
##	w[index] = z3.String("w_"+index)
##	w_bot[index] = z3.Bool("w_"+index+"_bot")
##	u = z3.String("u")
##	
##delta={}
##for word in domain:
##	for letter in inputalphabet:
##		delta[word][letter] = z3.Bool("delta_"+word+"_"+letter)


##eq21_1 = []
##for index in range(0,n):
##	eq21_1.append(
##		And(
##		(z3.UGE(z3.Length(u),index) == Not(v_bot[index])),
##		(z3.UGE(z3.Length(u),index) == Not(w_bot[index]))
##		)
##		)

##def_21.append(z3.And(eq21_1))


##eq21_2 = []
##for index in range(1,n):
##	for element1 in domain:
##		for element2 in domain:
##			for letter in inputalphabet:
##				if element2+letter in domain:
##					domain_eq21_2.append((
##								z3.Implies(z3.UGE(z3.Length(u),index),
##								z3.Or( z3.And( (v[index] == element1),
##								(v[index-1] == element2),
##								(z3.Select(u,index) == letter),
##								E[element1][element2+letter])
##								)
##								)
##								))

##def_21.append(z3.And(eq21_2))

##eq21_3 = [(v[0] == "")]

##def_21.append(z3.And(eq21_3))

##eq21_4 = []
##for element in domain:
##	for letter in inputalphabet:
##		eq21_4.append(
##		(z3.Concat(f[element],delta[element][letter]) == f[element+letter])
##		)

##def_21.append(z3.And(eq21_4))


##eq21_5 = []
##disj = []
##for index in range(1,n):
##	disj[index] = []
##	for element1 in domain:
##		for element2 in domain:
##			for letter in inputalphabet:
##				if element2+letter in domain:
##					disj[index].append(
##					z3.And(
##					(w[index] == element1),
##					(v[index-1] == element2),
##					(z3.Select(u,index) == letter),
##					(w[index] == delta[element2+letter])
##					))
##	eq21_5.append(And(
##	z3.Implies(
##	z3.UGE(z3.Length(u),i),
##	z3.Or(disj[index])
##	))



##def_21.append(z3.And(eq21_5))
##	
##eq21_6 = []
##for element1 in domain:
##	eq21_6.append(
##	Or( And( 
##	(v[n] == element1),
##	(z3.Concat(f[element1],w[out]) == Table[element1])
##	)



##def_21.append(z3.And(eq21_6))
##		
##############


##v = {}
##v_bot = {}
##for index in range(0,n):
##	v[index] = z3.String("v_"+index)
##	v_bot[index] = z3.Bool("v_"+index+"_bot")
##	

###How to handle the size of the real counterexample?
##eq21b_1 = []
##for index in range(0,n):
##	eq21b_1.append(
##	z3.And(
##	z3.Implies(z3.ULT(z3.Length(u),i),
##		v_bot[index])
##	))
##	


##eq21b_2 = []
##disj = []
##for index in range(1,n):
##	for element1 in domain:
##		for element2 in domain:
##			for letter in inputalphabet:
##				disj[letter] = []
##				if element2+letter in domain: 
##					disj[letter].append(
##					z3.And( (v[index] == element1),
##					(v[index-1] == element2),
##					(z3.Select(u,index) == letter),
##					E[element1][element2+letter]))
##				eq21b_2.append(
##				z3.And( 
##				z3.Implies(z3.UGE(z3.Length(u),i),
##				z3.Or( 
##				z3.Or(disj[letter]),
##				v_bot[index]
##				)
##				)))


##eq21_3 = (v[0] == ""))

##	
##domain_eq21b_3 = {}
##for element1 in domain:
##	for element2 in domain:
##		eq21b_3.append(
##		And( (v[n] == element2),
##		Implies(E[element1][element2],
##		Not(Table_bot[element1]))
##		))


#print(z3.solve(z3.And(def_eq,def_20)))

formula = []
formula.append(z3.And(outvalues))
formula.append(z3.And(def_eq))
formula.append(z3.And(def_20))

print(z3.solve(formula))
