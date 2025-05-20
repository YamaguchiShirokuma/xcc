#include <stdio.h>
int main (int argc, char *argv [])
{
    char last_op, *p = argv [1];
    printf (".data\n"
            "L_fmt:\n"
            "\t.ascii \"%%d\\n\\0\"\n"
            ".text\n"
            ".globl _main\n"
            "_main:\n"
            "\tpushq %%rbp\n"
            "\tmovq  %%rsp, %%rbp\n");

    printf ("\tmovl  $%c, %%ecx\n", *p++);
    last_op = *p++;
    printf ("\tmovl  $%c, %%edx\n", *p++);
    switch (last_op) {
    case '+':
        printf ("\taddl  %%edx, %%ecx\n");
        break;
    case '-':
        printf ("\tsubl  %%edx, %%ecx\n");
        break;
    }
    printf ("\tleaq L_fmt(%%rip), %%rdi\n"
            "\tmovslq %%ecx, %%rsi\n"
            "\tmovb $0, %%al\n"
            "\tcall  _printf\n"
            "\tleave\n"
            "\tret\n");
}

