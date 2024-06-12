#include <limits.h>

typedef struct
{
  int id;
  int age;
} Person;

/*@
  predicate unchanged{L1,L2}(Person *p, integer n) =
    \forall integer i; 0 <= i < n ==> \at(p[i].id, L1) == \at(p[i].id, L2);
*/

/*@
  requires \valid(p + (0 .. n-1));
  requires \forall int j; 0 <= j < n ==> p[j].age < INT_MAX;
  requires n > 0;

  assigns p[0 .. n-1];

  ensures \forall int j; 0 <= j < n ==> p[j].age == \at(p[j].age, Pre) + 1;

  ensures unchanged{Pre,Post}(p, n);
*/
void f(Person *p, int n)
{
  int i;

  /*@
    loop invariant 0 <= i <= n;

    loop invariant \forall int j; 0 <= j < n ==> \at(p[j].age, Pre) < INT_MAX; // Overflow pre
    loop invariant \forall int j; 0 <= j < i ==> p[j].age == \at(p[j].age, Pre) + 1; // Addition is valid for mutated elements
    loop invariant \forall int j; i <= j < n ==> p[j].age == \at(p[j].age, Pre); // Addition has not changed untouched elements

    loop invariant unchanged{Here, Pre}(p, n); // Unchanged elements are still unchanged

    loop assigns i, p[0 .. n-1];
    loop variant n - i;
  */
  for (i = 0; i < n; i++)
  {
    p[i].age += 1;
  }
}