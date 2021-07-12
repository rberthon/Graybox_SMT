
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
for element in domain:
	f[element] = z3.String("f_"+element)
	f_bot[element] = z3.Bool("f_"+element+"_bot")
	

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
		
################# lemma 20


def_20 = []

20_1 = []
for element1 in domain:
	for element2 in domain:
		20_1.append(
		And(
		Implies(f_bot[element1],
		Implies(f_bot[element2],E[element1][element2]
		)),
		Implies(f_bot[element1], 
		Implies(E[element1][element2],f_bot[element2]
		))
		)
		)

def_20.append(z3.And(20_1))

	
20_2 = []
for element1 in domain:
	for element2 in domain:
		if element1+element2 in domain :
			20_2.append(z3.Implies( 
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
				
def_20.append(z3.And(20_2))


domain_20_3 = []
for element in domain:
	for letter in inputalphabet:
		if element+letter in domain:
			domain_20_3.append(
			z3.Implies( 
			z3.Not(f_bot[element+letter])),
			z3.And(z3.Not(f_bot[element]),
			z3.PrefixOf(f[element],f[element+letter])
			)
			)
			

def_20.append(z3.And(20_3))


20_4 = []
for element1 in domain:
	for element2 in domain:
		for letter in inputalphabet:
			if (element1+letter in domain) and (element2+letter in domain):
				20_4.append
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


def_20.append(z3.And(20_4))


#lem_20_4 = And(Implies( And( Not(f1_bot),e12), And(e1a2a,Implies(Not(f1a_bot),And( StrPrefixOf(f1,f1a), StrPrefixOf(f2,f2a),Equals( StrSubstr(f1a,1+StrLength(f1),StrLength(f1a)-StrLength(f1)),StrSubstr(f2a,1+StrLength(f2),StrLength(f2a)-StrLength(f2)))))) for f1_bot,f1a_bot,f1,f2,f1a,f2a,e12,e1a2a in domain_20_4))

20_5 = []
for element1 in domain:
	for element2 in domain:
		20_5.append(
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

def_20.append(z3.And(20_5))


20_6 = []
conj = []
for element1 in domain:
	for letter in inputalphabet:
		if element1+letter in domain:
			conj[element1+letter] = []
			for element2 in domain:
				if element2+letter in domain:
					conj[element1+letter].append(z3.Not(E[element1][element2]))
			if conj[element1+letter] != []:
				20_6.append(
				z3.Implies( 
				z3.And(
				z3.Not(f_bot[element1+letter]),
				conj[element1+letter]
				),
				(f[element1] == f[element1+letter])
				))

def_20.append(z3.And(20_6))
				
################ lemma 21

n = 5 #Size of the word recognized here. This is temporary

def_21 = []

v = {}
v_bot = {}
w = {}
w_bot = {}
for index in range(0,n):
	v[index] = z3.String("v_"+index)
	v_bot[index] = z3.Bool("v_"+index+"_bot")
	w[index] = z3.String("w_"+index)
	w_bot[index] = z3.Bool("w_"+index+"_bot")
	u = z3.String("u")
	
delta={}
for word in domain:
	for letter in inputalphabet:
		delta[word][letter] = z3.Bool("delta_"+word+"_"+letter)


21_1 = []
for index in range(0,n):
	21_1.append(
		And(
		(z3.UGE(z3.Length(u),index) == Not(v_bot[index])),
		(z3.UGE(z3.Length(u),index) == Not(w_bot[index]))
		)
		)

def_21.append(z3.And(21_1))


21_2 = []
for index in range(1,n):
	for element1 in domain:
		for element2 in domain:
			for letter in inputalphabet:
				if element2+letter in domain:
					domain_21_2.append((
								z3.Implies(z3.UGE(z3.Length(u),index),
								z3.Or( z3.And( (v[index] == element1),
								(v[index-1] == element2),
								(z3.Extract(u,index,1) == letter),
								E[element1][element2+letter])
								)
								)
								))

def_21.append(z3.And(21_2))

21_3 = [(v[0] == "")]

def_21.append(z3.And(21_3))

21_4 = []
for element in domain:
	for letter in inputalphabet:
		21_4.append(
		(z3.Concat(f[element],delta[element][letter]) == f[element+letter])
		)

def_21.append(z3.And(21_4))


###############
#Current Point#
###############


#21_5 = []
#for index in range(1,n):
#	for element1 in domain:
#		for element2 in domain:
#			for letter in inputalphabet:
#				if element2+letter in domain:
#					domain_21_5.add((
#								eval(w[index]),
#								eval(v[index-1]),
#								index,
#								element1,
#								element2,
#								letter,
#								eval(delta[element2+letter])
#								),
#								i)
#						
#		
#		
#lem_21_5 = And(
#	Implies(BVUGE(StrLength(eval(u)),i),
#	Or( And( Equals(w_i,elem1),
#			Equals(v_i_minus,elem2),
#			Equals(StrCharAt(u,i),a),
#			Equals(w_i,d_v_i_a))
#		for v_i,w_i_minus,i,elem1,elem2,a,d_v_i_a in choice_index
#		)
#	)
#	for choice_index,i in domain_21_5
#	)		
#	
#	
#domain_21_6 = {}
#for element1 in domain:
#	domain_21_6.add(
#					eval(v[n]),
#					eval(w[out]),
#					element1,
#					eval(f[element1]),
#					Table[element1]
#					)
#		
#lem_21_6 = Or( And( Equals(v_n,elem1),
#			Equals(StrConcat(f_v_n,w_out),t_v_n),
#			Equals(w_i,d_v_i_a))
#		for v_n,w_out,elem1,f_v_n,t_v_n in domain_21_6
#		)
#		
############


#vb = {}
#vb_bot = {}
#for index in range(0,n):
#	v[index] = "v_"+index
#	v_bot[index] = "v_"+index+"_bot"
#	
#domain_21b_1 = {}
#for index in range(0,n):
#	domain_21b_1.add(
#		index,
#		eval(vb_bot[index]),
#		)
#	
##How to handle the size of the real counterexample?
#lem_21b_1 = And(
#	Implies( BVULT(StrLength(eval(u)),i),
#		v_bot)
#	for i,v_bot in domain_21b_1
#	)


#domain_21b_2 = {}
#for index in range(1,n):
#	for element1 in domain:
#		for element2 in domain:
#			for letter in inputalphabet:
#				if element2+letter in domain:
#					domain_21b_2.add((
#								eval(vb[index]),
#								eval(vb[index-1]),
#								index,
#								element1,
#								element2,
#								letter,
#								eval(E[element1][element2+letter])
#								),
#								eval(vb_bot[index]),
#								i)
#		
#lem_21b_2 = And( 
#	Implies(BVUGE(StrLength(eval(u)),i),
#	Or( Or(And( Equals(v_i,elem1),
#			Equals(v_i_minus,elem2),
#			Equals(StrCharAt(u,i),a),
#			e_1_2)
#		for v_i,v_i_minus,i,elem1,elem2,a,e_1_2 in choice_index
#		),
#		v_bot
#	)
#	)
#	for choice_index,v_bot,i in domain_21b_2
#)

#lem_21_3 = StrEquals(eval(v[0],""))



#	
#domain_21b_3 = {}
#for element1 in domain:
#	for element2 in domain:
#		domain_21b_3.add((
#					element2,
#					vb[n],
#					E[element1][element2],
#					Table_bot[element1]
#					),
#					eval(vb_bot[n])
#					)
#		
#lem_21b_3 = Or(
#	And( And( Equals(v_n,elem2),
#			Implies(e12,Not(t1))
#		)
#		for elem2,v_n,e12,t1 in choice_element
#	)
#	for choice_element,v_b in domain_21b_3
#	)

##print(solver.check() == z3.sat)
