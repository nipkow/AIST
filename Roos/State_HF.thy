theory State_HF
imports
  Chomsky_Schuetzenberger
  HereditarilyFinite.Finitary
begin

instantiation state :: (finitary) finitary
begin
  definition hf_of_state_def: 
    "hf_of \<equiv> case_state 0 1 (\<lambda>x. \<lbrace>\<lbrace>hf_of x\<rbrace>\<rbrace>)"
  instance 
    apply intro_classes
    by(auto simp: inj_on_def hf_of_state_def One_hf_def split: state.split_asm)
end

instantiation bracket :: finitary
begin
  definition hf_of_bracket_def: 
    "hf_of \<equiv> case_bracket 0 1"
  instance 
    apply intro_classes
    by(auto simp: inj_on_def hf_of_bracket_def split: bracket.split_asm)
end

instantiation version :: finitary
begin
  definition hf_of_version_def: 
    "hf_of \<equiv> case_version 0 1"
  instance 
    apply intro_classes
    by(auto simp: inj_on_def hf_of_version_def split: version.split_asm)
end

instantiation sym :: (finitary,finitary)finitary
begin
  definition hf_of_sym_def: 
    "hf_of \<equiv> case_sym (HF.Inl o hf_of) (HF.Inr o hf_of)"
  instance 
    apply intro_classes
    by(auto simp: inj_on_def hf_of_sym_def split: sym.split_asm)
end

end