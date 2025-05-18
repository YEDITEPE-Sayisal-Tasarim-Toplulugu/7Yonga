#include "games.h"

#include <stdint.h>
#include "csr.h"
#include "random.h"
#include "stdio.h"

void tahmin_oyunu(void) {
    srand(csr_read(time));
    
    int rand, us, skor;
    printf("Cikis icin 0 giriniz.\n\r\n\r");
    for (;;) {
        rand = random_mm(1, 1000);
        if (!rand) {srand(csr_read(time)); rand = random_mm(1, 1000);}
        skor = 0;
        for (;;) {
            printf("sayi gir: ");
            scanf("%d", &us);
            skor++;

            if (!us) {
                break;
            } else if (us == rand) {
                printf("\n\r%d deneme sonra kazandiniz.\n\r", skor);
                printf("Oyun tekrar baslatiliyor...\n\r");
                break;
            } else if (us > rand) {
                printf("\t- daha kucuk lutfen\n\r");
            } else {
                printf("\t- daha buyuk lutfen\n\r");
            }
        }

        if (!us) {
            break;
        }
    }

    printf("\n\relveda :/\n\r");
}

void fibonacci_main(int itr) {
    int a=0, b=1, temp;
    
    while (itr--) {
        temp = b;
        b += a;
        a = temp;

        printf("%d ", a);
    }
    printf("\n\r");
}