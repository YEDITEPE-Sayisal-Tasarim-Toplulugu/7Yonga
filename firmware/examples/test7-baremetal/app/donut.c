#include "donut.h"

#include <stdint.h>
#include "uart.h"
#include "string.h"

///////////////////////////// VERSION 1 ///////////////////////////////
/*
    https://www.a1k0n.net/2021/01/13/optimizing-donut.html
*/
#define R(mul,shift,x,y) \
    _=x; \
    x -= mul*y>>shift; \
    y += mul*_>>shift; \
    _ = (3145728-x*x-y*y)>>11; \
    x = x*_>>10; \
    y = y*_>>10;

int8_t b[1760], z[1760];

void donut_main(int frame_count)
{
	send_char('\n');
	send_char('\r');
    
	int sA=1024,cA=0,sB=1024,cB=0,_;

	for (int wq=0; wq<frame_count; wq++)
	{
        print_string("\033[2J");
        print_string("\033[0;0H");

        memset(b, 32, 1760);  // text buffer
        memset(z, 127, 1760);   // z buffer

        int sj=0, cj=1024;
        for (int j = 0; j < 90; j++) {
            int si = 0, ci = 1024;  // sine and cosine of angle i
            for (int i = 0; i < 324; i++) {
                int R1 = 1, R2 = 2048, K2 = 5120*1024;

                int x0 = R1*cj + R2,
                    x1 = ci*x0 >> 10,
                    x2 = cA*sj >> 10,
                    x3 = si*x0 >> 10,
                    x4 = R1*x2 - (sA*x3 >> 10),
                    x5 = sA*sj >> 10,
                    x6 = K2 + R1*1024*x5 + cA*x3,
                    x7 = cj*si >> 10,
                    x = 40 + 30*(cB*x1 - sB*x4)/x6,
                    y = 12 + 15*(cB*x4 + sB*x1)/x6,
                    N = (((-cA*x7 - cB*((-sA*x7>>10) + x2) - ci*(cj*sB >> 10)) >> 10) - x5) >> 7;

                int o = x + 80 * y;
                int8_t zz = (x6-K2)>>15;
                if (22 > y && y > 0 && x > 0 && 80 > x && zz < z[o]) {
                    z[o] = zz;
                    b[o] = ".,-~:;=!*#$@"[N > 0 ? N : 0];
                }
                R(5, 8, ci, si)  // rotate i
            }
            R(9, 7, cj, sj)  // rotate j
        }

        for (int k = 0; 1761 > k; k++)    
            if (k % 80)
                    send_char(b[k]);
            else
            {
                send_char('\n');
                send_char('\r');
            }
        
        R(5, 7, cA, sA);
        R(5, 8, cB, sB);
    }

    print_string("\n\rBitti.");
}
