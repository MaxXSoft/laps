int arr[20];

int qsort(int l, int r) {
  int i = l;
  int j = r;
  int p = arr[(l + r) / 2];
  while (i <= j) {
    while (arr[i] < p) i = i + 1;
    while (arr[j] > p) j = j - 1;
    if (i > j) break;
    int u = arr[i];
    arr[i] = arr[j];
    arr[j] = u;
    i = i + 1;
    j = j - 1;
  }
  if (i < r) qsort(i, r);
  if (j > l) qsort(l, j);
  return 0;
}

int main() {
  int i = 0;
  while (i < 20) {
    arr[i] = getint();
    i = i + 1;
  }
  qsort(0, 19);
  i = 0;
  while (i < 20) {
    putint(arr[i]);
    i = i + 1;
  }
  return 0;
}
