#include <stdint.h>

#define UART_BASE_ADDR 0x20000000
#define MAX_INT_BUFFER 15

char str[MAX_INT_BUFFER];

void putChar(char c) {
    *(volatile int*)(UART_BASE_ADDR+12) = c;
}

void putString(char *str) {
    while(*str) {
        putChar(*str);
        str++;
    }
}

void putInt(int num) {
    int i = 0, start, end;
    int isNegative = 0;

    // Handle 0 explicitly, otherwise empty string is printed
    if (num == 0) {
        str[i++] = '0';
        str[i] = '\0';
    } else {
        // Check if number is negative
        if (num < 0) {
            isNegative = 1;
            num = -num;
        }

        // Process each digit of the number
        while (num != 0) {
            int rem = num % 10;
            str[i++] = rem + '0';
            num = num / 10;
        }

        // Append '-' if the number is negative
        if (isNegative) {
            str[i++] = '-';
        }

        str[i] = '\0'; // Append string terminator

        // Reverse the string
        start = 0;
        end = i - 1;
        while (start < end) {
            char temp = str[start];
            str[start] = str[end];
            str[end] = temp;
            start++;
            end--;
        }
    }

    putString(str);
}

void putArray(int* array, int size) {
    int j;
    for (j=0; j<size; j++)
        putInt(array[j]);
}

int main( void )
{
    char* text = "abcdefgh";
    putString(text);
    putInt(123);

    return 0;
}