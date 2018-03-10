int fact(int n){
  if(n <= 1) return 1;
  return n * fact(n - 1);
}

int main() {
  putchar(fact(5) + '0');
  putchar(10);
  return 0;
}

