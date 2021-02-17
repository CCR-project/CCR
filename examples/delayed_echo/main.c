#include "stdio.h"
#include "stdlib.h"

struct Node {
  int val;
  struct Node* next;
};

void print_all(struct Node* ll) {
  if(ll) {
    printf("%d\t", ll->val);
    print_all(ll->next);
  }
  else {
    printf("\n");
  }
}

struct Node* push(struct Node* ll, int x) {
  struct Node* new_node = malloc(sizeof(struct Node));
  new_node->val = x;
  new_node->next = ll;
  printf("[DEBUG]: ");
  print_all(new_node);
  return new_node;
}







struct Node* my_list = NULL;

void echo() {
  int n;
  scanf("%d", &n);
  if(n == -1) {
    printf("ECHO ENDS WITH: ");
    print_all(my_list);
    return;
  }
  my_list = push(my_list, n);
  echo();
}

int main() {
  echo();
}
