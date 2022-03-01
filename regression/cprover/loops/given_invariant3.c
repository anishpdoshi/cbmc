int x;

int main()
{
  for(x=0; x<100; x++)
    __CPROVER_loop_invariant(x>=0 && x<=100)
  {
    // whatnot
  }

  __CPROVER_assert(x == 100, "non-inductive property");

  return 0;
}
