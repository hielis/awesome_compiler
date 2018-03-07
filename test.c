
int fact(int n) {
  if (n <= 1) return 1;
  return n * fact(n-1);
}

int main() {
  int n;
  n = 0;
  fact(3);
  putchar(10);
  return 0;
}
