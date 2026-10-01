#!/usr/bin/env python3
"""Emit exact rational data and kernel-checked matrix multiplication proofs.
The generated Lean declarations are self-contained; this generator is not trusted.
"""
from fractions import Fraction as F
from pathlib import Path
H=[[F(0),F(1),F(1,20)],[F(1),F(0),F(1,10)],[F(1,20),F(1,10),F(0)]]
L=[[H[i][k]*(j==l)-(i==k)*H[l][j] for k in range(3) for l in range(3)] for i in range(3) for j in range(3)]
def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(a))) for j in range(len(a))] for i in range(len(a))]
def q(x):return f'({x.numerator}/{x.denominator} : ℂ)'
def vec(xs):return '!['+','.join(xs)+']'
def matrix(a,kind):
 if kind=='h':return '!!['+';\n'.join(','.join(q(x) for x in r) for r in a)+']'
 return '(fun a b => ('+vec([vec([vec([vec([q(a[3*i+j][3*k+l]) for l in range(3)]) for k in range(3)]) for j in range(3)]) for i in range(3)])+' : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) a.1 a.2 b.1 b.2)'
out=['import Krylov.PowerNormCertificate','', 'namespace Krylov.RationalPowerCertificates','open Matrix PerturbedDynamics','open scoped BigOperators','noncomputable section','set_option maxHeartbeats 8000000','set_option maxRecDepth 4000', 'abbrev I := Fin 3 × Fin 3','def H : Matrix (Fin 3) (Fin 3) ℂ := complexHamiltonian (1/20)','def L : Matrix I I ℂ := commutatorMatrix H']
for kind,base,ns,typ in [('h',H,[2,4],'Matrix (Fin 3) (Fin 3) ℂ'),('l',L,[2,4,8,16,32],'Matrix I I ℂ')]:
 A=base
 for n in ns:
  A=mul(A,A);name=f'{kind}{n}';base_name=kind.upper()
  out += [f'\ndef {name} : {typ} :=\n'+matrix(A,kind),f'theorem {name}_eq : {base_name}^{n} = {name} := by']
  if n==2:out += ['  rw [pow_two]']
  else:out += [f'  rw [show ({n} : ℕ)={n//2}+{n//2} from rfl,pow_add,{kind}{n//2}_eq]']
  if kind=='h':out+=['  ext i j; fin_cases i <;> fin_cases j <;>']
  else:out+=['  ext ⟨i,j⟩ ⟨k,l⟩; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>']
  deps=[name] + ([f'{kind}{n//2}'] if n>2 else ['H','L','complexHamiltonian','commutatorMatrix','Perturbation.hamiltonian'])
  if kind=='l' and n==2:
   out += ["    simp only [Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_succ,Fin.sum_univ_zero,",
           "      L,commutatorMatrix,Fin.ext_iff,Fin.val_ofNat',Fin.val_mk,Fin.val_succ,Fin.val_zero,Fin.val_one] <;>",
           "    norm_num [l2,H,complexHamiltonian,Perturbation.hamiltonian,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]"]
  else:
   out+=['    norm_num ['+','.join(deps+['Matrix.mul_apply','Fintype.sum_prod_type','Fin.sum_univ_succ'])+']']
  S=sum(x*x for row in A for x in row)
  out += [f'theorem {name}_frobenius : (∑ i,∑ j,‖({base_name}^{n}) i j‖^2) = ({S.numerator}/{S.denominator} : ℝ) := by',f'  rw [{name}_eq]', '  simp_rw [← Complex.normSq_eq_norm_sq]',f'  norm_num [{name},Fintype.sum_prod_type,Fin.sum_univ_succ,Complex.normSq_apply]']
out+=['\ntheorem H_norm : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3) H‖ ≤ 11/10 := by','  apply PowerNormCertificate.norm_le_of_power_frobenius H (complexHamiltonian_hermitian _) 2 (11/10) (by norm_num)','  norm_num only [show (2:ℕ)^2=4 from rfl]','  rw [h4_frobenius]','  norm_num','\ntheorem L_norm : ‖liouvillian H‖ ≤ 11/5 := by','  apply PowerNormCertificate.norm_le_of_power_frobenius L (commutatorMatrix_hermitian _ (complexHamiltonian_hermitian _)) 2 (11/5) (by norm_num)','  norm_num only [show (2:ℕ)^2=4 from rfl]','  rw [l4_frobenius]','  norm_num','end','end Krylov.RationalPowerCertificates']
Path('Krylov/RationalPowerCertificates.lean').write_text(
    '\n'.join(out)+'\n', encoding='utf-8', newline='\n')
