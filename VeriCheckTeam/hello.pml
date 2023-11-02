
int v = 0;

active proctype main() {
  printf("Hello world\n");

  if
    ::true -> { v = 1; printf("v = %d\n", v); };
    ::true -> { v = -2; printf("v = %d\n", v); };
  fi
}

ltl {[] (v >= 0)}