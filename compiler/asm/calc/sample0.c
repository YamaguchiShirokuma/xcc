#include <stdio.h>
int main (int argc, char *argv [])
{
    char last_op, *p = argv [1];
    int  num1, num2, acc;

    num1    = *p++ - '0';
    last_op = *p++;
    num2    = *p++ - '0';
    switch (last_op) {
    case '+':
        acc = num1 + num2;
        break;
    case '-':
        acc = num1 - num2;
        break;
    }

    printf ("%d\n", acc);
}

