int printf();
long i;
long sum;

long mod(long x, long y) { return x - (x / y) * y; }

int main() {
  i = 5;
  sum = 0;
  while (0 < i) {
    printf("i = %ld\n", i);
    sum = sum + i;
    i = i - 1;
  }
  sum = mod(sum, 4);
  printf("sum = %ld\n", sum);
}
