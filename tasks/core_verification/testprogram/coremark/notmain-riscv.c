#include <stdint.h>

#include "port\core_portme.h"
#include "coremark\coremark.h"

float notmain(void)
{
	main();
	return(0);
}