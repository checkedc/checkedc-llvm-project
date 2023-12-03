typedef char CHAR16;

int
FindAccessVariable (_Nt_array_ptr<CHAR16> VariableName) {
  return -1;
}

int
mineVariableServiceGetVariable (
CHAR16 *VariableName : itype(_Nt_array_ptr<CHAR16>)) {
return FindAccessVariable (VariableName);
}
