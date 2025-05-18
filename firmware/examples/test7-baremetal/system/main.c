#include <stdint.h>
#include "csr.h"
#include "stdio.h"
#include "string.h"
#include "uart.h"
#include "timer.h"

#include "games.h"
#include "donut.h"

#define COMMAND_BUFFER_SIZE         120
volatile char comamnd_buffer[COMMAND_BUFFER_SIZE];

int get_argument(char *com, int n, char type, void *ptr, int limit) {
    int arg_length = 10;
    char arg_buffer[10] = {0}; // arg_buffer'ı sıfırladık.

    // Aranan argümanı bul
    while (*com && n) {
        if (*com == ' ') n--;
        com++;
    }

    if (n) return 0; // Eğer n hala 0 değilse, aranan sıraya ulaşılamadı.

    // Argümanı doldur
    if (type == 'c') {
        *(char*)ptr = *com;
        return (limit > 0);
    } else if (type == 's') {
        while (*com && limit) {
            *(char*)ptr++ = *com++;
            limit--;
        }
        *(char*)ptr = '\0'; // Null-terminate string
        return (!(*com));
    } else if (type == 'd') {
        while (*com && arg_length) {
            arg_buffer[10 - arg_length] = *com++;
            arg_length--;
        }
        *(int*)ptr = atoi(arg_buffer);
        return (!(*com));
    } else {
        return 0; // Desteklenmeyen tür
    }
}

void shell(void) {
    for (;;){
        printf("$ ");
        scanf("%s", comamnd_buffer);
        printf("\ncommand: %s\n", comamnd_buffer);
        
        if (!strncmp((char *)(comamnd_buffer), "exit", 4)) {
            printf("bye..\n");
            break;
        } else if (!strncmp((char *)(comamnd_buffer), "help", 4)) {
            printf("\n\rRISC-V x32 IMFAB\n\rF(C) 2024\n\r\n\r");
            printf("commands:\n\r");
            printf("\thelp\t\tyardim\n\r");
            printf("\texit\t\tcikis\n\r");
            printf("\tdonut\t\tdonut ciz\n\r");
            printf("\tgame1\t\ttahmin oyunu\n\r");
        } else if (!strncmp((char *)(comamnd_buffer), "time", 4)) {
            printf("time: %d\n\r", csr_read(time));
        } else if (!strncmp((char *)(comamnd_buffer), "game1", 5)) {
            tahmin_oyunu();
        } else if (!strncmp((char *)(comamnd_buffer), "donut", 5)) {
            int itr;
            if (get_argument((char *)comamnd_buffer, 1, 'd', &itr, 1)) {
                printf("%d adet frame üret.\n\r", itr);
                donut_main(itr);
            } else {
                printf("kaç frame?");
            }
        } else if (!strncmp((char *)(comamnd_buffer), "set baude", 9)) {
            int baude_arg = 9600;
            int baude_div;
            get_argument((char *)comamnd_buffer, 2, 'd', &baude_arg, 1);
            baude_div = (CLOCK_FREQ * 1000000) / baude_arg - 1;
            printf("new baude_rate = %d\n", baude_arg);
            printf("new baude_div = %d\n", baude_div);
            while (!uart_tx_empty())
                ;
            uart_set_baude_rate(baude_div);
        } else if (!strncmp((char *)(comamnd_buffer), "fibonacci", 9)) {
            int itr;
            if (get_argument((char *)comamnd_buffer, 1, 'd', &itr, 1)) {
                printf("%d adet sayi üret.\n\r", itr);
                fibonacci_main(itr);
            } else {
                printf("kaç sayı lazim?");
            }
        } else {
            printf("tanımadım ben bunu.\n");
        }

        printf("\n\r");
    }
}

int main ( void ) {

    char *str1 = "RISC-V X32 IMFAB\n\r";
    char *str2 = "F(C) 2024\n\r";
	
	print_string(str1);
	print_string(str2);
    
    shell();

    return 0;
}