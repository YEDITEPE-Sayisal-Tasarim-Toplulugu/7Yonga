#include <stdint.h>

#define UART_BASE_ADDR 0x20000000

int array[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
volatile char INT_ARRAY[32];

void intToStr(int num, volatile char str[]) {
    int isNegative = 0;
    int i = 0;
    
    // Handle negative integers
    if (num < 0) {
        isNegative = 1;
        num = -num;
    }

    // Convert integer to string
    do {
        str[i++] = (num % 10) + '0';
        num /= 10;
    } while (num > 0);
    
    // Add negative sign if necessary
    if (isNegative) {
        str[i++] = '-';
    }

    // Null-terminate the string
    str[i] = '\0';

    // Reverse the string
    int start = 0;
    int end = i - 1;
    char temp;
    while (start < end) {
        temp = str[start];
        str[start] = str[end];
        str[end] = temp;
        start++;
        end--;
    }
}

void putInt(int s)
{
    int i;
    // *(volatile int*)(UART_BASE_ADDR+12) = s;
    intToStr(s, INT_ARRAY);

    for (i=0; INT_ARRAY[i]; i++) {
        *(volatile int*)(UART_BASE_ADDR+12) = INT_ARRAY[i];
    }
}

void putArray(int* array, int size)
{
    int j;
    for (j=0; j<size; j++)
        putInt(array[j]);
}

int main( void )
{
    int n = sizeof(array)/sizeof(array[0]);
    int i;

    for (i=0; i<n; i++)
    {
        if (array[i] & 1)
            array[i] = -1;
        else
            array[i] = 1;
    }

    putArray(array, n);

    return 0;
}