struct tagA { int c; int d; };
int foo() {
  return 2;
}
int main() {
  struct { int a, b; } arr[2][1];
  int d = arr[0][foo() + 3].a;
  return d + arr[0][0].b;
}
