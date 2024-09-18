
#include "win_stdio.h"
#include "win_string.h"
#include "win_misc.h"

extern "C" __stdcall char *GetCommandLineA(void);
//extern "C" long long InterlockedExchangeAdd64(volatile long long * ptr, long long  val);

extern "C" __stdcall unsigned long GetTickCount();
extern "C" unsigned long mach_absolute_time() {	
	return GetTickCount();
}

extern "C" void* mach_host_self()
{
	return 0;
}

extern "C" int host_statistics()
{
	return -1;		// returning an error code
}

extern "C" void uuid_generate_random()
{
	printf("NYI uuid_generate_random\n");
}

extern "C" int mach_timebase_info(void *) 
{
	printf("NYI mach_timebase_info\n");
	return 0;
}

extern const char ldVersionString[];
#define BUILD_STR "LD64 port (951_9) " 
const char ldVersionString[] = BUILD_STR;// "[" __DATE__ ":" __TIME__ "] ";

extern "C" int _NSGetExecutablePath(char *buf, unsigned int *bufSize)
{
	char *arg = GetCommandLineA();
	char *eow = strchr(arg, ' ');
	if (eow)
	{
		if ((eow - arg) > (*bufSize - 1))
		{
			*bufSize = (eow - arg) + 1;
			return -1;
		}
		strncpy(buf, arg, (eow - arg));
		buf[(eow - arg)] = 0;
		return 0;
	}
	else
	{
		return -1;
	}
}

extern "C"
void __assert_rtn(const char* func, const char* file, int line, const char* failedexpr)
{
	printf("__assert_rtn: %s, %s, %d, %s\n", func, file, line, failedexpr);
	exit(1);
}



