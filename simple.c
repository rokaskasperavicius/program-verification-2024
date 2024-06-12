/*@
  assigns \nothing;
  ensures \result == l;
*/
int f(int h, int l)
{
  return l;
}

/*@
  ensures \forall int h, l; \result == 1;
*/
int f_self_composed(int h, int l)
{
  int oL = f(0, l);
  int oH = f(h, l);
  return oL == oH;
}