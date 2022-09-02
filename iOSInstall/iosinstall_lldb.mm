#import <Carbon/Carbon.h>
#import <CoreFoundation/CoreFoundation.h>
#import <Cocoa/Cocoa.h>
#include <unistd.h>
#include <dirent.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <stdio.h>
#include <signal.h>
#include <getopt.h>
#include <pwd.h>
#include <dlfcn.h>
#include <wchar.h>
#include "mobiledevice.h"

#define FDVENDOR_PATH  "/tmp/iosinstall-remote-debugserver"
#define PREP_CMDS_PATH "/tmp/iosinstall-gdb-prep-cmds"
#define LLDB_PREP_CMDS_PATH "/tmp/iosinstall-lldb-prep-cmds"
#define PREP_CMDS_PATH_WITH_X "-x /tmp/iosinstall-gdb-prep-cmds"
#define LLDB_PREP_CMDS_PATH_WITH_S "-s /tmp/iosinstall-lldb-prep-cmds"

// iosgdb prep file
#define GDB_PREP_CMDS CFSTR("set mi-show-protections off\n\
    set auto-raise-load-levels 1\n\
    set shlib-path-substitutions /usr \"{ds_path}/Symbols/usr\" /System \"{ds_path}/Symbols/System\" \"{device_container}\" \"{disk_container}\" \"/private{device_container}\" \"{disk_container}\" /Developer \"{ds_path}/Symbols/Developer\"\n\
    set remote max-packet-size 1024\n\
    set sharedlibrary check-uuids on\n\
    set env NSUnbufferedIO YES\n\
    set minimal-signal-handling 1\n\
    set sharedlibrary load-rules \\\".*\\\" \\\".*\\\" container\n\
    set inferior-auto-start-dyld 0\n\
    file \"{disk_app}\"\n\
    set remote executable-directory {device_app}\n\
    set remote noack-mode 1\n\
    set trust-readonly-sections 1\n\
    target remote-mobile " FDVENDOR_PATH"-{device_id}-{username}\n\
    mem 0x1000 0x3fffffff cache\n\
    mem 0x40000000 0xffffffff none\n\
    mem 0x00000000 0x0fff none\n\
    set minimal-signal-handling 0\n\
    set inferior-auto-start-cfm off\n\
    set sharedLibrary load-rules dyld \".*libobjc.*\" all dyld \".*CoreFoundation.*\" all dyld \".*Foundation.*\" all dyld \".*libSystem.*\" all dyld \".*AppKit.*\" all dyld \".*PBGDBIntrospectionSupport.*\" all dyld \".*/usr/lib/dyld.*\" all dyld \".*libSystem.*\" all dyld \".*CarbonDataFormatters.*\" all dyld \".*libauto.*\" all dyld \".*CFDataFormatters.*\" all dyld \"/System/Library/Frameworks/.*\" extern dyld \"/System/Library/PrivateFrameworks\" extern dyld \"/usr/lib\" extern dyld \".*\" all exec \".*\" all\n\
    set host-charset UTF-8\n\
    set language auto\n\
    sharedlibrary apply-load-rules all\n\
    set inferior-auto-start-dyld 1\n")

//    run {args}\n\
//    set sharedLibrary load-rules dyld ".*AppKit.*" all dyld ".*libobjc.*" all dyld ".*CarbonDataFormatters.*" all dyld ".*libauto.*" all dyld ".*PBGDBIntrospectionSupport.*" all dyld ".*CFDataFormatters.*" all dyld ".*CoreFoundation.*" all dyld ".*libSystem.*" all dyld ".*/usr/lib/dyld.*" all dyld ".*Foundation.*" all dyld "/System/Library/Frameworks/.*" extern dyld "/System/Library/PrivateFrameworks/.*" extern dyld "/usr/lib.*" extern dyld ".*" all exec ".*" all 

// lldb prep file
#define LLDB_PREP_CMDS CFSTR("\
platform select remote-ios --sysroot \"{symbols_path}\"\n\
target create \"{disk_app}\"\n\
script iosinstall_device_app=\"{device_app}\"\n\
script iosinstall_connect_url=\"connect://127.0.0.1:{device_port}\"\n\
target modules search-paths add /usr \"{symbols_path}/usr\" /System \"{symbols_path}/System\" \"/private{device_container}\" \"{disk_container}\" \"{device_container}\" \"{disk_container}\" /Developer \"{symbols_path}/Developer\"\n\
command script import \"{python_file_path}\"\n\
command script add -f {python_command}.connect_command connect\n\
command script add -s asynchronous -f {python_command}.run_command run\n\
command script add -s asynchronous -f {python_command}.safequit_command safequit\n\
settings set target.memory-module-load-level minimal\n\
connect\n\
")


#define LLDB_IOSINSTALL_MODULE CFSTR("\
import lldb\n\
import sys\n\
import os\n\
import shlex\n\
\n\
def connect_command(debugger, command, result, internal_dict):\n\
    # These two are passed in by the script which loads us\n\
    connect_url = internal_dict['iosinstall_connect_url']\n\
    error = lldb.SBError()\n\
\n\
    # Create and set listener for iosinstall\n\
    listener = lldb.SBListener(\"ioinstall listener\")\n\
    listener.StartListeningForEventClass(lldb.target.GetDebugger(), lldb.SBProcess.GetBroadcasterClassName(), lldb.SBProcess.eBroadcastBitStateChanged)\n\
\n\
    process = lldb.target.ConnectRemote(listener, connect_url, None, error)\n\
\n\
    # Wait for connection to succeed\n\
    state = (process.GetState() or lldb.eStateInvalid)\n\
    while state != lldb.eStateConnected:\n\
        event = lldb.SBEvent()\n\
        if listener.WaitForEvent(1, event):\n\
            state = process.GetStateFromEvent(event)\n\
        else:\n\
            state = lldb.eStateInvalid\n\
\n\
    # Stop listening\n\
    listener.StopListeningForEventClass(lldb.target.GetDebugger(), lldb.SBProcess.GetBroadcasterClassName(), lldb.SBProcess.eBroadcastBitStateChanged)\n\
\n\
    print('Target connected')\n\
    device_app = internal_dict['iosinstall_device_app']\n\
    lldb.target.modules[0].SetPlatformFileSpec(lldb.SBFileSpec(device_app))\n\
    print('Process ready to launch')\n\
\n\
\n\
def run_command(debugger, command, result, internal_dict):\n\
    device_app = internal_dict['iosinstall_device_app']\n\
    error = lldb.SBError()\n\
    lldb.target.modules[0].SetPlatformFileSpec(lldb.SBFileSpec(device_app))\n\
    launch_info = lldb.SBLaunchInfo(shlex.split('{args}'))\n\
    lldb.target.Launch(launch_info, error)\n\
    lockedstr = ': Locked'\n\
    if lockedstr in str(error):\n\
       print('\\nDevice Locked\\n')\n\
       sys.exit(254)\n\
    else:\n\
       print(str(error))\n\
\n\
\n\
def safequit_command(debugger, command, result, internal_dict):\n\
    process = lldb.target.process\n\
    state = process.GetState()\n\
    if state == lldb.eStateRunning:\n\
       process.Detach()\n\
       os._exit(0)\n\
    elif state > lldb.eStateRunning:\n\
       os._exit(state)\n\
    else:\n\
       print('\\nApplication has not been launched\\n')\n\
       os._exit(1)\n\
")


//Global options and variables
int op_uninstall = 0;
int op_run = 0;
int op_install = 0;
int op_list = 0;
int op_view = 0;
int op_mount = 0;

am_device_notification_callback chosen_callback = NULL;

bool found_device = false;
bool debug = false;
bool silent = false;
bool forward = false;
double   physconntimeout = 0; //Dev phys connection timeout in seconds
int  xcodemajor = 0;
int  xcodeminor = 0;
char *image_path = NULL;
wchar_t *launcher_path = NULL;
char *launcher_options[64];
int launcheroptcnt = 0;
wchar_t *app_path = NULL;
CFStringRef app_bundleID = NULL;
char *device_id = NULL;
char *args = NULL;
CFStringRef last_path = NULL;
struct am_device_notification *notify;
int gdbfd;
ServiceConnRef dbgServiceConnection = NULL;

char prepbuf[PATH_MAX];

//Device phys connection
CFRunLoopSourceRef source;
CFRunLoopSourceContext source_context;
CFRunLoopTimerRef timer;
CFRunLoopTimerContext timer_context;

//Max number of app arguments
#define MAX_APP_ARGS 100
//App arguments string
const char *appargs[MAX_APP_ARGS];
int appargc=0;
const char** appargv;

//Xcode selected path
char xcpath[2048];
int xcode_found_via_xclib = 0;

//Package type - IPA (detected) or developer bundle (default)
int isIPA = 0;

//lldb related
int port = 0;
int islauncherlldb = 0;
const char* lldb_prep_justlaunch_cmds = "\
    run\n\
    safequit\n\
";
CFSocketRef server_socket;
CFSocketRef lldb_socket;
CFSocketNativeHandle lldb_socket_handle = -1;
CFWriteStreamRef serverWriteStream = NULL;
CFWriteStreamRef lldbWriteStream = NULL;
char *target_arch = "armv7";
CFStringRef version;
CFStringRef build;
CFStringRef device_support_path_root;
wchar_t *customprepfile_path = NULL;

//Helpers
static char* Copy_CFStringRefToCString(const CFStringRef pCFStringRef)
{
    char* results = NULL;

    if (NULL != pCFStringRef)
    {
        // Make sure what calculated buf length is enough for strings with 
        // each char encoded as two UTF-16 pairs - i.e. 4 bytes for each char
        CFIndex length = 2 * sizeof(UniChar) * CFStringGetLength(pCFStringRef);

        results = (char*) NewPtrClear(length);

        if (!CFStringGetCString(pCFStringRef,results,length,kCFStringEncodingASCII))
        {
            if (CFStringGetCString(pCFStringRef,results,length,kCFStringEncodingUTF8))
            {
                return results;
            }
            else 
            {
                DisposePtr(results);
                results = NULL;
            }
        }
    }
    return results;
}

Boolean path_exists(CFTypeRef path, Boolean isDirectory) {
    if (CFGetTypeID(path) == CFStringGetTypeID()) {
        CFURLRef url = CFURLCreateWithFileSystemPath(NULL, (CFStringRef)path, kCFURLPOSIXPathStyle, isDirectory);
        Boolean result = CFURLResourceIsReachable(url, NULL);
        CFRelease(url);
        return result;
    } else if (CFGetTypeID(path) == CFURLGetTypeID()) {
        return CFURLResourceIsReachable((CFURLRef)path, NULL);
    } else {
        return false;
    }
}

char tohex(int x)
{
    static char* hexchars = "0123456789ABCDEF";
    return hexchars[x];
}

unsigned int fromhex(char c)
{
    if (c >= '0' && c <= '9')
        return c - '0';
    else if (c >= 'a' && c <= 'f')
        return 10 + c - 'a';
    else if (c >= 'A' && c <= 'F')
        return 10 + c - 'A';
    else
        return 0;
}
//End Helpers

void disable_ssl(ServiceConnRef con)
{
    // MobileDevice links with SSL, so function will be available;
    typedef void (*SSL_free_t)(void*);
    static SSL_free_t SSL_free = NULL;
    if (SSL_free == NULL)
    {
        SSL_free = (SSL_free_t)dlsym(RTLD_DEFAULT, "SSL_free");
    }

    SSL_free(con->sslContext);
    con->sslContext = NULL;
}

//RSP packets
void send_str(char* buf, int fd)
{
    int bytes = 0;
    bytes = write(fd, buf, strlen(buf));
    if(!silent)
        printf("send: bytes=%d (%s)\n", bytes, buf);
}

// Flag for indicating app stopped by some reason (SIGKILL received etc)
// Used in detection alternative app ending on device - not normal exit condition, Run Without Debug only.
// In Run With Debug case app life cycle controlled by debugger
static int appthreadstopped = 0;

int recv_pkt(int fd)
{
    int bytes = 0;
    char buf[16*1024];
    bytes = read(fd, buf, sizeof(buf)-1);

    if(!silent)
        printf("recv: bytes=%d\n", bytes);
    if (bytes >= 0)
        buf[bytes] = 0x00;
    if(!silent)
        printf("d='%s'\n", buf);
    if (strstr(buf, "metype:") != NULL)
       appthreadstopped = 1;      
    if (bytes > 0 && buf[0] == '$') 
    {
        send_str("+", fd);
        // Check if received packet is app output and NOT response to thread run request
        if ((bytes > 1 && buf[1] == 'O') &&
           strcmp(buf,"$OK#9a"))
        {
            char* c = buf+2;
            char* bufend = buf+strlen(buf);
            int i = 0;
            if (!silent)
               printf("recv: data='");
            while (*c != '#' && c < bufend) 
            {
                buf[i] = fromhex(*c++) << 4;
                buf[i] |= fromhex(*c++);
                if (!silent)
                    printf ("%c",buf[i]);
                else if (silent && forward)
                    printf ("%c",buf[i]);
                if (buf[i] > 0 && buf[i] != 0x0d)
                    i++; 
            }
            if (!silent)
               printf("'\n");
            fflush(stderr);
            fflush(stdout);
        }
    }
    return bytes;
}

void send_pkt(char* buf, int fd)
{
    int i;
    unsigned char csum = 0;
    char *buf2 = (char*)malloc (32*1024);
    int cnt = strlen (buf);
    char *p;

    p = buf2;
    *p++ = '$';

    for (i = 0; i < cnt; i++)
    {
        csum += buf[i];
        *p++ = buf[i];
    }
    *p++ = '#';
    *p++ = tohex ((csum >> 4) & 0xf);
    *p++ = tohex (csum & 0xf);

    *p = '\0';

    int bytes = 0;
    bytes = write(fd, buf2, strlen(buf2));
    if(!silent)
        printf("send: bytes=%d (%s)\n", bytes, buf);
    free(buf2);
}
//End RSP packets


void fdvendor_callback(CFSocketRef s, CFSocketCallBackType callbackType, CFDataRef address, const void *data, void *info) 
{
    CFSocketNativeHandle socket = (CFSocketNativeHandle)(*((CFSocketNativeHandle *)data));

    struct msghdr message;
    struct iovec iov[1];
    struct cmsghdr *control_message = NULL;
//  To avoid error: size of array 'ctrl_buf' is not an integral constant-expression 
//  we should use malloc instead of static buffer
//  char ctrl_buf[CMSG_SPACE(sizeof(int))];
    char *ctrl_buf = (char*)malloc(CMSG_SPACE(sizeof(int)));
    char dummy_data[1];

    memset(&message, 0, sizeof(struct msghdr));
    memset(ctrl_buf, 0, CMSG_SPACE(sizeof(int)));

    dummy_data[0] = ' ';
    iov[0].iov_base = dummy_data;
    iov[0].iov_len = sizeof(dummy_data);

    message.msg_name = NULL;
    message.msg_namelen = 0;
    message.msg_iov = iov;
    message.msg_iovlen = 1;
    message.msg_controllen = CMSG_SPACE(sizeof(int));
    message.msg_control = ctrl_buf;

    control_message = CMSG_FIRSTHDR(&message);
    control_message->cmsg_level = SOL_SOCKET;
    control_message->cmsg_type = SCM_RIGHTS;
    control_message->cmsg_len = CMSG_LEN(sizeof(int));

    *((int *) CMSG_DATA(control_message)) = gdbfd;

    sendmsg(socket, &message, 0);
	free(ctrl_buf);
    CFSocketInvalidate(s);
    CFRelease(s);
}

void lldb_callback(CFSocketRef s, CFSocketCallBackType callbackType, CFDataRef address, const void *data, void *info);

void fdvendor_callback_lldb (CFSocketRef s, CFSocketCallBackType callbackType, CFDataRef address, const void *data, void *info) 
{
    CFSocketNativeHandle socket = (CFSocketNativeHandle)(*((CFSocketNativeHandle *)data));

    assert (callbackType == kCFSocketAcceptCallBack);

    lldb_socket  = CFSocketCreateWithNative(NULL, socket, kCFSocketDataCallBack, &lldb_callback, NULL);
    int flag = 1;
    int res = setsockopt(socket, IPPROTO_TCP, TCP_NODELAY, (char *) &flag, sizeof(flag));
    assert (res == 0);

    lldb_socket_handle = CFSocketGetNative (lldb_socket);
    CFRunLoopAddSource(CFRunLoopGetMain(), CFSocketCreateRunLoopSource(NULL, lldb_socket, 0), kCFRunLoopCommonModes);

    CFSocketInvalidate(s);
    CFRelease(s);
}

CFStringRef copy_device_support_path(AMDeviceRef device, int search4DMG) 
{
    struct passwd *passwd;
    char *iosdeviceimage = 0;
    char version_majmin[16];
    char *version_majminStrPtr;
    char *p;

    //get current user details
    passwd = getpwuid(getuid());

    version = AMDeviceCopyValue(device, 0, CFSTR("ProductVersion"));
    build = AMDeviceCopyValue(device, 0, CFSTR("BuildVersion"));

    // Create major.minor version
    version_majminStrPtr = Copy_CFStringRefToCString(version);
    strncpy(version_majmin, version_majminStrPtr, sizeof(version_majmin) - 1);
    version_majmin[sizeof(version_majmin) - 1] = 0;
    DisposePtr(version_majminStrPtr);

    p = strchr(version_majmin, '.');
    if(p != NULL) {
        p = strchr(p + 1, '.');
        if(p != NULL) {
          *p = 0;
        }
    }

    if (!silent) {                                                                                                                                                                        
        char *versionStrPtr = Copy_CFStringRefToCString(version);
        char *buildStrPtr = Copy_CFStringRefToCString(build);
        printf("Device reported:\tProduct version %s (Build version %s). Major.Minor=%s\n", versionStrPtr, buildStrPtr,  version_majmin);                                                                                                                                                  
        DisposePtr(versionStrPtr);                                                                                                                                                                                     
        DisposePtr(buildStrPtr);                                                                                                                                                                                     
    }

    //Checking if device support path specified explicitly in env variable
    if((iosdeviceimage = getenv("IOSDEVICEIMAGE")) != NULL) {
        if (!silent) {
            printf("User specified device support path: %s\n", iosdeviceimage);                                                                                                                                                  
        }                                                                                                                                                                        
    }

    const char* home = passwd->pw_dir; //user home, we shouldn't rely on any foreign env vars
    CFStringRef path = NULL;
    bool found = false;

    if(iosdeviceimage != NULL) {
        path = CFStringCreateWithFormat(NULL, NULL, CFSTR("%s"), iosdeviceimage);
        //Check if user path not really exists on fs
        found = path_exists(path, true);
        if (!found) {
            printf("err=User specified device support path not exists on host\n");                                                                                                                                                          
            exit(1);
        }
    } else {
        if (!silent) {
            printf("warn=User not specified device support path, automatic choice will used\n");                                                                                                                                                  
        }                                                                                                                                                                        
    }

    //Searching for libs used for cross debugging

    //Device has different version than SDK ?
    if ((!found) && (!search4DMG))
    {
        path = CFStringCreateWithFormat(NULL, NULL, CFSTR("%s/Library/Developer/Xcode/iOS DeviceSupport/%@ (%@) arm64e"), home, version, build);
	device_support_path_root = CFStringCreateWithFormat(NULL, NULL, CFSTR("%s/Library/Developer/Xcode/iOS DeviceSupport"), home);
        found = path_exists(path, true);
    }
    if ((!found) && (!search4DMG))
    {
        path = CFStringCreateWithFormat(NULL, NULL, CFSTR("%s/Library/Developer/Xcode/iOS DeviceSupport/%@ (%@)"), home, version, build);
	device_support_path_root = CFStringCreateWithFormat(NULL, NULL, CFSTR("%s/Library/Developer/Xcode/iOS DeviceSupport"), home);
        found = path_exists(path, true);
    }
    if ((!found) && (!search4DMG))
    {
        path = CFStringCreateWithFormat(NULL, NULL, CFSTR("%s/Library/Developer/Xcode/iOS DeviceSupport/%@"), home, version);
	device_support_path_root = CFStringCreateWithFormat(NULL, NULL, CFSTR("%s/Library/Developer/Xcode/iOS DeviceSupport"), home);
        found = path_exists(path, true);
    }
    if ((!found) && (!search4DMG))
    {
        path = CFStringCreateWithFormat(NULL, NULL, CFSTR("%s/Library/Developer/Xcode/iOS DeviceSupport/%s"), home, version_majmin);
	device_support_path_root = CFStringCreateWithFormat(NULL, NULL, CFSTR("%s/Library/Developer/Xcode/iOS DeviceSupport"), home);
        found = path_exists(path, true);
    }
    //Device has exact version with installed SDK ?
    if ((!found) && (!search4DMG))
    {
        if(!xcode_found_via_xclib) {
            path = CFStringCreateWithFormat(NULL, NULL, CFSTR("/Applications/Xcode.app/Contents/Developer/Platforms/iPhoneOS.platform/DeviceSupport/%@ (%@)"), version, build);
	    device_support_path_root = CFStringCreateWithFormat(NULL, NULL, CFSTR("/Applications/Xcode.app/Contents/Developer/Platforms/iPhoneOS.platform/DeviceSupport"));
	}
        else {
            path = CFStringCreateWithFormat(NULL, NULL, CFSTR("%s/Platforms/iPhoneOS.platform/DeviceSupport/%@ (%@)"), &xcpath[2], version, build);
	    device_support_path_root = CFStringCreateWithFormat(NULL, NULL, CFSTR("%s/Platforms/iPhoneOS.platform/DeviceSupport"), &xcpath[2]);
	}
        found = path_exists(path, true);
    }

    //We searching for DMG

    // Xcode version >= 4.3 
    if ((!found) && (search4DMG))
    {
        struct dirent **uuiddirlist;
        int n;
        char buf[4096];
    
        if(!xcode_found_via_xclib)
            sprintf(buf, "%s","/Applications/Xcode.app/Contents/Developer/Platforms/iPhoneOS.platform/DeviceSupport");
        else
            sprintf(buf, "%s%s", &xcpath[2] ,"/Platforms/iPhoneOS.platform/DeviceSupport");
        
        if (!silent)
          printf("Searching for device support DMG in %s\n", buf);
        
        n = scandir(buf, &uuiddirlist, 0, alphasort);
    
        if(n<0) {
            printf("warn=Xcode device support path does not exist on host - please check Xcode installation\n");                                                                                                                                                        
        }
        else if (n>0){
            while(n-- && !found) {
                //Exclude upper and root dirs
                if(strcmp(uuiddirlist[n]->d_name, "..") && 
                   strcmp(uuiddirlist[n]->d_name, ".") &&
                   strcmp(uuiddirlist[n]->d_name, ".DS_Store"))
                {
                    sprintf(buf, "Discovered DMG path: %s", uuiddirlist[n]->d_name);
                    if (!silent)
                      printf("%s\n", buf);
    
                    if(strstr(uuiddirlist[n]->d_name, version_majmin)) {
                      if(!xcode_found_via_xclib)
                          sprintf(buf, "%s/%s", "/Applications/Xcode.app/Contents/Developer/Platforms/iPhoneOS.platform/DeviceSupport", 
                                           uuiddirlist[n]->d_name);
                      else
                          sprintf(buf, "%s%s/%s", &xcpath[2], "/Platforms/iPhoneOS.platform/DeviceSupport",
                                           uuiddirlist[n]->d_name);                                           
                      path = CFStringCreateWithCString(NULL, buf, kCFStringEncodingASCII);
                      if (!silent)
                        printf("Matched DMG directory found : %s\n", buf);
                      found = true;
                    }
                }
                free(uuiddirlist[n]);
            }
            free(uuiddirlist);
        }
    }    

    // Xcode version < 4.3 
    if((!found) && (search4DMG)) {
        struct dirent **uuiddirlist;
        int n;
        char buf[512];
    
        if(!xcode_found_via_xclib)
            sprintf(buf, "%s","/Developer/Platforms/iPhoneOS.platform/DeviceSupport");
        else
            sprintf(buf, "%s%s", &xcpath[2] ,"/Platforms/iPhoneOS.platform/DeviceSupport");

        if (!silent)
          printf("Searching for device support DMG in %s\n", buf);
        
        n = scandir(buf, &uuiddirlist, 0, alphasort);
    
        if(n<0) {
            printf("warn=Xcode version < 4.3 device support path does not exist on host - please check Xcode installation under /Developer\n");                                                                                                                                                         
        }
        else if (n>0){
            while(n-- && !found) {
                //Exclude upper and root dirs
                if(strcmp(uuiddirlist[n]->d_name, "..") && 
                   strcmp(uuiddirlist[n]->d_name, ".") &&
                   strcmp(uuiddirlist[n]->d_name, ".DS_Store"))
                {
                    sprintf(buf, "Discovered DMG path: %s", uuiddirlist[n]->d_name);
                    if (!silent)
                      printf("%s\n", buf);
    
                    if(strstr(uuiddirlist[n]->d_name, version_majmin)) {
                      if(!xcode_found_via_xclib)
                          sprintf(buf, "%s/%s", "/Developer/Platforms/iPhoneOS.platform/DeviceSupport", 
                                           uuiddirlist[n]->d_name);                       
                      else
                          sprintf(buf, "%s%s/%s", &xcpath[2], "/Platforms/iPhoneOS.platform/DeviceSupport",
                                           uuiddirlist[n]->d_name);                       
                      path = CFStringCreateWithCString(NULL, buf, kCFStringEncodingASCII);
                      if (!silent)
                        printf("Matched DMG directory found : %s\n", buf);
                      found = true;
                    }
                }
                free(uuiddirlist[n]);
            }
            free(uuiddirlist);
        }
    }    

    if(found && !search4DMG) {
        if (!silent) {                                                                                                                                                                        
            char *foundPathStrPtr = Copy_CFStringRefToCString(path);
            printf("Device support path found: %s\n", foundPathStrPtr );                                                                                                                                                  
            DisposePtr(foundPathStrPtr);                                                                                                                                                                                     
        }
    }

//    CFRelease(version);
//    CFRelease(build);

    if (!found)
    {
        if ((path != NULL) && (CFStringGetLength(path) != 0))
            CFRelease(path);
        printf("err=Unable to locate DeviceSupport directory for the connected device. Please check Xcode installation path and run Xcode Devices.\n");
        exit(1);
    }

    return path;
}

void fixup_device_id(char *data)
{
  char ch;

  do {
    ch = *data++;
    if (ch == '-') 
      *(data-1) = '_';
  } while (ch != '\0');
}

void write_lldb_prep_cmds(AMDeviceRef device, CFURLRef disk_app_url, CFURLRef device_app_url) 
{
    struct passwd *passwd;

    //get current user details
    passwd = getpwuid(getuid());

    CFStringRef ds_path = copy_device_support_path(device, 0);
    CFStringRef symbols_path = CFStringCreateWithFormat(NULL, NULL, CFSTR("%@/Symbols"), ds_path);

    CFMutableStringRef cmds = CFStringCreateMutableCopy(NULL, 0, LLDB_PREP_CMDS);
    CFRange range = { 0, CFStringGetLength(cmds) };

// platform select remote-ios --sysroot {symbols_path}

    CFStringFindAndReplace(cmds, CFSTR("{symbols_path}"), symbols_path, range, 0);
    range.length = CFStringGetLength(cmds);

    CFMutableStringRef pmodule = CFStringCreateMutableCopy(NULL, 0, LLDB_IOSINSTALL_MODULE);

    CFRange rangeLLDB = { 0, CFStringGetLength(pmodule) };

    if (args) {
        CFStringRef cf_args = CFStringCreateWithCString(NULL, args, kCFStringEncodingUTF8);
        CFStringFindAndReplace(cmds, CFSTR("{args}"), cf_args, range, 0);
        rangeLLDB.length = CFStringGetLength(pmodule);
        CFStringFindAndReplace(pmodule, CFSTR("{args}"), cf_args, rangeLLDB, 0);

        CFRelease(cf_args);
    } else {
        CFStringFindAndReplace(cmds, CFSTR("{args}"), CFSTR(""), range, 0);
        rangeLLDB.length = CFStringGetLength(pmodule);
        CFStringFindAndReplace(pmodule, CFSTR("{args}"), CFSTR(""), rangeLLDB, 0);
    }
    range.length = CFStringGetLength(cmds);

    CFStringRef device_app_path = CFURLCopyFileSystemPath(device_app_url, kCFURLPOSIXPathStyle);
    CFStringFindAndReplace(cmds, CFSTR("{device_app}"), device_app_path, range, 0);
    range.length = CFStringGetLength(cmds);

    CFStringRef disk_app_path = CFURLCopyFileSystemPath(disk_app_url, kCFURLPOSIXPathStyle);
    CFStringFindAndReplace(cmds, CFSTR("{disk_app}"), disk_app_path, range, 0);
    range.length = CFStringGetLength(cmds);

    CFStringRef device_port = CFStringCreateWithFormat(NULL, NULL, CFSTR("%d"), port);
    CFStringFindAndReplace(cmds, CFSTR("{device_port}"), device_port, range, 0);
    range.length = CFStringGetLength(cmds);

    CFURLRef device_container_url = CFURLCreateCopyDeletingLastPathComponent(NULL, device_app_url);
    CFStringRef device_container_path = CFURLCopyFileSystemPath(device_container_url, kCFURLPOSIXPathStyle);
    CFMutableStringRef dcp_noprivate = CFStringCreateMutableCopy(NULL, 0, device_container_path);
    range.length = CFStringGetLength(dcp_noprivate);
    CFStringFindAndReplace(dcp_noprivate, CFSTR("/private/var/"), CFSTR("/var/"), range, 0);
    range.length = CFStringGetLength(cmds);
    CFStringFindAndReplace(cmds, CFSTR("{device_container}"), dcp_noprivate, range, 0);
    range.length = CFStringGetLength(cmds);

    CFURLRef disk_container_url = CFURLCreateCopyDeletingLastPathComponent(NULL, disk_app_url);
    CFStringRef disk_container_path = CFURLCopyFileSystemPath(disk_container_url, kCFURLPOSIXPathStyle);
    CFStringFindAndReplace(cmds, CFSTR("{disk_container}"), disk_container_path, range, 0);
    range.length = CFStringGetLength(cmds);

    char python_file_path[300] = "/tmp/iosinstall_";
    char python_command[300] = "iosinstall_";
    if(device_id != NULL) {
        strcat(python_file_path, device_id);
        strcat(python_command, device_id);

        fixup_device_id(python_file_path);
        fixup_device_id(python_command);
    }
    strcat(python_file_path, ".py");

    CFStringRef cf_python_command = CFStringCreateWithCString(NULL, python_command, kCFStringEncodingASCII);
    CFStringFindAndReplace(cmds, CFSTR("{python_command}"), cf_python_command, range, 0);
    range.length = CFStringGetLength(cmds);
    CFStringRef cf_python_file_path = CFStringCreateWithCString(NULL, python_file_path, kCFStringEncodingUTF8);
    CFStringFindAndReplace(cmds, CFSTR("{python_file_path}"), cf_python_file_path, range, 0);
    range.length = CFStringGetLength(cmds);

    CFDataRef cmds_data = CFStringCreateExternalRepresentation(NULL, cmds, kCFStringEncodingUTF8, 0);

	if(launcher_path) {
        char preppathbuf[512];
        const char* extra_cmds = lldb_prep_justlaunch_cmds;

		//create unique prep file for current user
		sprintf(preppathbuf, "%s-%s", LLDB_PREP_CMDS_PATH, passwd->pw_name);

		FILE *out = fopen(preppathbuf, "w");
		if(NULL == out) {
		   printf("err=Prep file cannot be opened for writing at %s\n", preppathbuf);
		   exit(1);
		}
		fwrite(CFDataGetBytePtr(cmds_data), CFDataGetLength(cmds_data), 1, out);
        if(!debug) {
           fwrite(extra_cmds, strlen(extra_cmds), 1, out);
        }
        fclose(out);

		//Print prepared prep commands to stdout
        if(!silent) {
            printf("<prepcmds>");
            fwrite(CFDataGetBytePtr(cmds_data), CFDataGetLength(cmds_data), 1, stdout);
            if(!debug) {
                fwrite(extra_cmds, strlen(extra_cmds), 1, stdout);
            }
            printf("</prepcmds>\n");                                                   
        }

		// User provided his custom prep file ?
		if (customprepfile_path != NULL)
		{
            char custompreppathbuf[1024];

			// Test custom prep file for reading
        	FILE *cpf = fopen((const char*)customprepfile_path, "r");
        	if (NULL == cpf) {
           		printf("err=Can't open user specified custom prep file for read at %s\n", customprepfile_path);
           		exit(1);
        	} 
			else                                        
				fclose(cpf);
            if(!silent)
				printf("warn=Append user custom prep file to startup prep file: %s >> %s\n", customprepfile_path, preppathbuf);
            sprintf(custompreppathbuf, "cat %s >> %s", customprepfile_path, preppathbuf);                                                           
            system(custompreppathbuf);  // append user custom prep file to startup prep file                                                              	
		}

	    CFDataRef pmodule_data = CFStringCreateExternalRepresentation(NULL, pmodule, kCFStringEncodingUTF8, 0);

	    out = fopen(python_file_path, "w");
	    fwrite(CFDataGetBytePtr(pmodule_data), CFDataGetLength(pmodule_data), 1, out);
	    fclose(out);
    } else {
        //Automated run with LLDB.
        char prep_cmds_path[512] = LLDB_PREP_CMDS_PATH;
        
        //Create temp directory at same level with app bundle and place LLDB prep file into it
        char *disk_container_pathStr = Copy_CFStringRefToCString(disk_container_path);
        char *app_bundle_name = Copy_CFStringRefToCString(CFURLCopyLastPathComponent(disk_app_url));
        
        if(!silent)
            printf("App bundle container dir: %s\n", disk_container_pathStr);
        sprintf(prepbuf,"%s/%s",disk_container_pathStr, "temp-dir");
        if(!mkdir(prepbuf, 0755) || errno == EEXIST) {
            strcat(prepbuf, "/iosinstall-lldb-prep-cmds-");
            strcat(prepbuf, app_bundle_name);
            FILE *out = fopen(prepbuf, "w");
            if(NULL == out) {
                printf("err=Can't open prep cmds file for writing in %s\n",disk_container_pathStr);
                exit(1);
            }
            fwrite(CFDataGetBytePtr(cmds_data), CFDataGetLength(cmds_data), 1, out);   
            fclose(out);                                                               

		    CFDataRef pmodule_data = CFStringCreateExternalRepresentation(NULL, pmodule, kCFStringEncodingUTF8, 0);
		    out = fopen(python_file_path, "w");
		    fwrite(CFDataGetBytePtr(pmodule_data), CFDataGetLength(pmodule_data), 1, out);
		    fclose(out);
        } else {
            printf("err=Can't create temp dir for prep cmds file in %s: %s\n",disk_container_pathStr, strerror(errno));
            exit(1);
        }
        DisposePtr(disk_container_pathStr);
        DisposePtr(app_bundle_name);
	} 

    CFRelease(cmds);
    if (ds_path != NULL) CFRelease(ds_path);
    CFRelease(device_app_path);
    CFRelease(disk_app_path);
    CFRelease(device_container_url);
    CFRelease(device_container_path);
    CFRelease(dcp_noprivate);
    CFRelease(disk_container_url);
    CFRelease(disk_container_path);
    CFRelease(cmds_data);
    CFRelease(cf_python_command);
    CFRelease(cf_python_file_path);
}

void write_gdb_prep_cmds(AMDeviceRef device, CFURLRef disk_app_url, CFStringRef bundle_identifier, CFURLRef device_app_url) 
{
    char argstr[4096];
    CFMutableStringRef cmds = CFStringCreateMutableCopy(NULL, 0, GDB_PREP_CMDS);
    CFRange range = { 0, CFStringGetLength(cmds) };
    struct passwd *passwd;

    //get current user details
    passwd = getpwuid(getuid());

    CFStringFindAndReplace(cmds, CFSTR("{device_id}"), CFStringCreateWithCString(NULL, device_id, kCFStringEncodingASCII), range, 0);
    range.length = CFStringGetLength(cmds);

    CFStringFindAndReplace(cmds, CFSTR("{username}"), CFStringCreateWithCString(NULL, passwd->pw_name, kCFStringEncodingASCII), range, 0);
    range.length = CFStringGetLength(cmds);

    CFStringRef ds_path = copy_device_support_path(device, 0);
    CFStringFindAndReplace(cmds, CFSTR("{ds_path}"), ds_path, range, 0);
    range.length = CFStringGetLength(cmds);

    if (args) {
        CFStringRef cf_args = CFStringCreateWithCString(NULL, args, kCFStringEncodingASCII);
        CFStringFindAndReplace(cmds, CFSTR("{args}"), cf_args, range, 0);
        CFRelease(cf_args);
    } else {
        CFStringFindAndReplace(cmds, CFSTR(" {args}"), CFSTR(""), range, 0);
    }
    range.length = CFStringGetLength(cmds);

    CFStringRef device_app_path = CFURLCopyFileSystemPath(device_app_url, kCFURLPOSIXPathStyle);
    CFStringFindAndReplace(cmds, CFSTR("{device_app}"), device_app_path, range, 0);
    range.length = CFStringGetLength(cmds);

    CFStringRef disk_app_path = CFURLCopyFileSystemPath(disk_app_url, kCFURLPOSIXPathStyle);
    CFStringFindAndReplace(cmds, CFSTR("{disk_app}"), disk_app_path, range, 0);
    range.length = CFStringGetLength(cmds);

    CFURLRef device_container_url = CFURLCreateCopyDeletingLastPathComponent(NULL, device_app_url);
    CFStringRef device_container_path = CFURLCopyFileSystemPath(device_container_url, kCFURLPOSIXPathStyle);
    CFMutableStringRef dcp_noprivate = CFStringCreateMutableCopy(NULL, 0, device_container_path);
    range.length = CFStringGetLength(dcp_noprivate);
    CFStringFindAndReplace(dcp_noprivate, CFSTR("/private/var/"), CFSTR("/var/"), range, 0);
    range.length = CFStringGetLength(cmds);
    CFStringFindAndReplace(cmds, CFSTR("{device_container}"), dcp_noprivate, range, 0);
    range.length = CFStringGetLength(cmds);

    CFURLRef disk_container_url = CFURLCreateCopyDeletingLastPathComponent(NULL, disk_app_url);
    CFStringRef disk_container_path = CFURLCopyFileSystemPath(disk_container_url, kCFURLPOSIXPathStyle);
    CFStringFindAndReplace(cmds, CFSTR("{disk_container}"), disk_container_path, range, 0);

    CFDataRef cmds_data = CFStringCreateExternalRepresentation(NULL, cmds, kCFStringEncodingUTF8, 0);

    if(launcher_path) {
        char preppathbuf[256];

        //create unique prep file for current user 
        sprintf(preppathbuf, "%s-%s", PREP_CMDS_PATH, passwd->pw_name);

        FILE *out = fopen(preppathbuf, "w");
        if(NULL == out) {
           printf("err=Prep file cannot be opened for writing at %s\n", preppathbuf);
           exit(1);
        }                                        
        fwrite(CFDataGetBytePtr(cmds_data), CFDataGetLength(cmds_data), 1, out);
        //Adding app arguments, if were specified
        if (appargc > 0)
        {
          int count;
          char* p = argstr;
          sprintf(p, "set args ");
          p += strlen(p);
          for (count = 0; count < appargc; count++) {
            if(!silent)
                printf("warn=app argv[%d] = %s\n", count, appargv[count]);
            sprintf(p, "\"%s\" ", appargv[count]);
            p += strlen(p);                                                                       
          }
          fwrite(argstr, strlen(argstr), 1, out);
        }
        //Print prepared prep commands to stdout                                   
        printf("<prepcmds>");                                                      
        fwrite(CFDataGetBytePtr(cmds_data), CFDataGetLength(cmds_data), 1, stdout);
        if (appargc > 0)
          fwrite(argstr, strlen(argstr), 1, stdout);
        printf("</prepcmds>\n");                                                   
        fclose(out);                                                               
    } else {
        //Automated run with GDB.
        //Create temp directory at same level with app bundle and place GDB prep file into it
        char *disk_container_pathStr = Copy_CFStringRefToCString(disk_container_path);
        char *app_bundle_name = Copy_CFStringRefToCString(CFURLCopyLastPathComponent(disk_app_url));

        if(!silent)
            printf("App bundle container dir: %s\n", disk_container_pathStr);
        sprintf(prepbuf,"%s/%s",disk_container_pathStr, "temp-dir");
        if(!mkdir(prepbuf, 0755) || errno == EEXIST) {
            strcat(prepbuf, "/iosinstall-gdb-prep-cmds-");
            strcat(prepbuf, app_bundle_name);
            FILE *out = fopen(prepbuf, "w");
            if(NULL == out) {
                printf("err=Can't open prep cmds file for writing in %s\n",disk_container_pathStr);
                exit(1);
            }
            fwrite(CFDataGetBytePtr(cmds_data), CFDataGetLength(cmds_data), 1, out);   
            //Adding app arguments, if were specified
            if (appargc > 0)
            {
              int count;
              char* p = argstr;
              sprintf(p, "set args ");
              p += strlen(p);
              for (count = 0; count < appargc; count++) {
                if(!silent)
                    printf("warn=app argv[%d] = %s\n", count, appargv[count]);
                sprintf(p, "\"%s\" ", appargv[count]);
                p += strlen(p);                                                                       
              }
              fwrite(argstr, strlen(argstr), 1, out);
            }
            fclose(out);                                                               
        } else {
            printf("err=Can't create temp dir for prep cmds file in %s: %s\n",disk_container_pathStr, strerror(errno));
            exit(1);
        }
        DisposePtr(disk_container_pathStr);
        DisposePtr(app_bundle_name);
    }

    CFRelease(cmds);
    if (ds_path != NULL) CFRelease(ds_path);
    CFRelease(device_app_path);
    CFRelease(disk_app_path);
    CFRelease(device_container_url);
    CFRelease(device_container_path);
    CFRelease(dcp_noprivate);
    CFRelease(disk_container_url);
    CFRelease(disk_container_path);
    CFRelease(cmds_data);
}

AMDeviceRef globaldevice=NULL;

void stop_app_handler(int signum)
{
    //Write RSP commands directly to opened gdbfd
    {
        if(!silent)                                                                       
            printf("Target stop via RSP\n");                                                       

        char* cmds[] = {                                                                        
            "\x03",                                                                              
            NULL                                                                              
        };                                                                                    
                                                                                       
        char** cmd = cmds;                                                                    
        while (*cmd) {                                                                        
            send_pkt(*cmd, gdbfd);                                                            
//            recv_pkt(gdbfd); //No target response expected                                                                 
            cmd++;                                                                            
        }                                                                                     
    }
    // No asserts - session may be already dead here
    AMDeviceStopSession(globaldevice);
    AMDeviceDisconnect(globaldevice);
    close(gdbfd);
    _exit(0);
}

void
server_callback (CFSocketRef s, CFSocketCallBackType callbackType, CFDataRef address, const void *data, void *info)
{
    char buffer[0x1000];
    int bytesRead = AMDServiceConnectionReceive(dbgServiceConnection, buffer, sizeof(buffer));
    if (bytesRead == 0)
    {
        // close the socket on which we've got end-of-file, the server_socket.
        CFSocketInvalidate(s);
        CFRelease(s);
        return;
    }
    write(CFSocketGetNative (lldb_socket), buffer, bytesRead);
    while (bytesRead == sizeof(buffer))
    {
        bytesRead = AMDServiceConnectionReceive(dbgServiceConnection, buffer, sizeof(buffer));
        if (bytesRead > 0)
        {
            write(CFSocketGetNative (lldb_socket), buffer, bytesRead);
        }
    }
}

void lldb_callback(CFSocketRef s, CFSocketCallBackType callbackType, CFDataRef address, const void *data, void *info)
{
    if (CFDataGetLength ((CFDataRef)data) == 0) {
        // close the socket on which we've got end-of-file, the lldb_socket.
        CFSocketInvalidate(s);
        CFRelease(s);
        return;
    }
    AMDServiceConnectionSend(dbgServiceConnection, CFDataGetBytePtr((CFDataRef)data),  CFDataGetLength ((CFDataRef)data));
}

void start_remote_debug_server(AMDeviceRef device) 
{
    mode_t oldmask;
    struct passwd *passwd;
    char fdvendorpath[256];

	if (!islauncherlldb)
	{
        //get current user details
        passwd = getpwuid(getuid());
        sprintf(fdvendorpath, "%s-%s-%s", FDVENDOR_PATH, device_id, passwd->pw_name);
        
        oldmask = umask(0000); // Set socket permisions to *777
        
        CFSocketRef fdvendor = CFSocketCreate(NULL, AF_UNIX, 0, 0, kCFSocketAcceptCallBack, &fdvendor_callback, NULL);
                                                                                                                      
        struct sockaddr_un address;                                                                                   
        memset(&address, 0, sizeof(address));                                                                         
        address.sun_family = AF_UNIX;                                                                                 
        strcpy(address.sun_path, fdvendorpath);                                                                      
        address.sun_len = SUN_LEN(&address);                                                                          
        CFDataRef address_data = CFDataCreate(NULL, (const UInt8 *)&address, sizeof(address));                        
                                                                                                                      
        unlink(fdvendorpath);                                                                                        
        
        sleep(2);
                                                                                                                      
        CFSocketSetAddress(fdvendor, address_data);                                                                   
        CFRelease(address_data);                                                                                      
        CFRunLoopAddSource(CFRunLoopGetMain(), CFSocketCreateRunLoopSource(NULL, fdvendor, 0), kCFRunLoopCommonModes);
        
        umask(oldmask); 
        
        globaldevice = device;
        signal(SIGQUIT, stop_app_handler);
	}
	else
	{
        /*
         * The debugserver connection is through a fd handle, while lldb requires a host/port to connect, so create an intermediate
         * socket to transfer data.
         */
        server_socket = CFSocketCreateWithNative (NULL, gdbfd, kCFSocketReadCallBack, &server_callback, NULL);
        CFRunLoopAddSource(CFRunLoopGetMain(), CFSocketCreateRunLoopSource(NULL, server_socket, 0), kCFRunLoopCommonModes);
        
        struct sockaddr_in addr4;
        memset(&addr4, 0, sizeof(addr4));
        addr4.sin_len = sizeof(addr4);
        addr4.sin_family = AF_INET;
        addr4.sin_port = htons(port);
        addr4.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
        
        CFSocketRef fdvendor = CFSocketCreate(NULL, PF_INET, 0, 0, kCFSocketAcceptCallBack, &fdvendor_callback_lldb, NULL);

        if (port) {           
          int yes = 1;
          setsockopt(CFSocketGetNative(fdvendor), SOL_SOCKET, SO_REUSEADDR, &yes, sizeof(yes));
        }

        CFDataRef address_data = CFDataCreate(NULL, (const UInt8 *)&addr4, sizeof(addr4));
        
        CFSocketSetAddress(fdvendor, address_data);
        CFRelease(address_data);
        socklen_t addrlen = sizeof(addr4);
        int res = getsockname(CFSocketGetNative(fdvendor),(struct sockaddr *)&addr4,&addrlen);
        assert(res == 0);
        port = ntohs(addr4.sin_port);

        CFRunLoopAddSource(CFRunLoopGetMain(), CFSocketCreateRunLoopSource(NULL, fdvendor, 0), kCFRunLoopCommonModes);        
    }                                                           
}

void stdin_callback(CFSocketRef s, CFSocketCallBackType type, CFDataRef address, const void *data, void *info)
{
    FILE    *stdinfp = (FILE*)info;
    char buf[1024];
    int buflen = 0;

    if (fgets(buf, sizeof(buf), stdinfp) == NULL)
            return; //Nothing on stdin

    buflen = strlen(buf);
    if (buf[buflen-1] == '\n') 
        // remove the newline
        buf[buflen-1] = '\0';
    else
        return;

    //Write RSP commands directly to opened gdbfd
    {
        if(!silent)                                                                       
            printf("Target stop via RSP\n");                                                       

        char* cmds[] = {                                                                        
            "\x03",                                                                              
            NULL                                                                              
        };                                                                                    
                                                                                       
        char** cmd = cmds;                                                                    
        while (*cmd) {                                                                        
            send_pkt(*cmd, gdbfd);                                                            
//            recv_pkt(gdbfd); //No target response expected                                                                 
            cmd++;                                                                            
        }                                                                                     
    }
}

void add_stdin_runloop_callback(void) 
{
    CFSocketRef         in;
    CFSocketContext     context = { 0, stdin, NULL, NULL, NULL };
    CFRunLoopSourceRef  ins;

    // Create a "socket" reference with the file descriptor associated with stdin
    in  = CFSocketCreateWithNative(NULL,
                       STDIN_FILENO,
                       kCFSocketReadCallBack,
                       stdin_callback,
                       &context);

    // Create a run loop source for the (stdin) file descriptor
    ins = CFSocketCreateRunLoopSource(NULL, in, 0/*nesting*/);

    // add stdin source to the run loop 
    CFRunLoopAddSource(CFRunLoopGetCurrent(), ins, kCFRunLoopDefaultMode);

    CFRelease(ins);
    CFRelease(in);
}

void transfer_callback(CFDictionaryRef dict, int arg) 
{
    int percent;

        CFStringRef status = (CFStringRef)CFDictionaryGetValue(dict, CFSTR("Status"));                                                      
        CFNumberGetValue((CFNumberRef)CFDictionaryGetValue(dict, CFSTR("PercentComplete")), kCFNumberSInt32Type, &percent);                 
                                                                                                                               
        if (CFEqual(status, CFSTR("CopyingFile"))) {                                                                           
            CFStringRef path = (CFStringRef)CFDictionaryGetValue(dict, CFSTR("Path"));                                                      
                                                                                                                               
            if ((last_path == NULL || !CFEqual(path, last_path)) && !CFStringHasSuffix(path, CFSTR(".ipa"))) {                 
                if(!silent) {
                    char localBuffer[1024];
                    memset ( (void *) localBuffer, 0, sizeof(localBuffer)); 
                    Boolean conversion_fine;
                    conversion_fine = CFStringGetCString(path, localBuffer, sizeof(localBuffer), kCFStringEncodingUTF8);
                    if (conversion_fine == TRUE) 
                       printf("[%3d%%] Copying %s to device\n", percent / 2, localBuffer); 
                    else
                       printf("[%3d%%] Copying %s to device\n", percent / 2, "app bundle item"); 
                }
            }                                                                                                                  
                                                                                                                               
            if (last_path != NULL) {                                                                                           
                CFRelease(last_path);                                                                                          
            }                                                                                                                  
            last_path = CFStringCreateCopy(NULL, path);                                                                        
        }                                                                                                                      
}

void install_callback(CFDictionaryRef dict, int arg) {
    int percent;

        CFStringRef status = (CFStringRef)CFDictionaryGetValue(dict, CFSTR("Status"));                                      
        CFNumberGetValue((CFNumberRef)CFDictionaryGetValue(dict, CFSTR("PercentComplete")), kCFNumberSInt32Type, &percent); 
        if(!silent)                                                                                                         
            printf("[%3d%%] %s\n", (percent / 2) + 50, CFStringGetCStringPtr(status, kCFStringEncodingMacRoman));  
}

bool lookup_applications(AMDeviceRef device, CFDictionaryRef* result) {
   
    static const int n_lookups = 5;
    for (int i_lookup = 0; i_lookup < n_lookups; i_lookup++) {
        
        if (AMDeviceLookupApplications(device, 0, result) == 0)
            return true;
       
        printf("err=Installed applications lookup failed (attempt %d of %d in %d secs)\n", 
                i_lookup+1, n_lookups, (i_lookup+1)*5);
        sleep(5);
    }      
    return false;
} 

void handle_device(AMDeviceRef device) {

    if (found_device) 
            return; // handle session with one device only 
    
    CFStringRef found_device_id = AMDeviceCopyDeviceIdentifier(device);
    char *found_device_id_StrPtr = Copy_CFStringRefToCString(found_device_id);

    if (device_id != NULL) {
        if((found_device_id_StrPtr !=NULL) && 
           (strcmp(device_id, found_device_id_StrPtr) == 0)) {
            found_device = true;
        } else {
            if(NULL != found_device_id_StrPtr)
              DisposePtr(found_device_id_StrPtr);
            return;
        }
    } else {
        found_device = true;
    }

    CFRetain(device); // don't know if this is necessary?

    if(!silent)
        printf("[  0%%] Found device (%s), beginning install\n", found_device_id_StrPtr);

    AMDeviceConnect(device);
    if (!(AMDeviceIsPaired(device) && 
         (AMDeviceValidatePairing(device) == 0) &&
         (AMDeviceStartSession(device) == 0))) 
    {
        printf("err=Can't start session with device (UDID: %s). Please check if your Mac set as trusted computer on device.\n", 
               found_device_id_StrPtr);
        exit(1);
    }

    if(NULL != found_device_id_StrPtr)
        DisposePtr(found_device_id_StrPtr);

    CFStringRef path = CFStringCreateWithCString(NULL, (const char *)app_path, kCFStringEncodingUTF8);
    CFURLRef relative_url = CFURLCreateWithFileSystemPath(NULL, path, kCFURLPOSIXPathStyle, false);
    CFURLRef url = CFURLCopyAbsoluteURL(relative_url);

    CFRelease(relative_url);

    CFStringRef keys[] = { CFSTR("PackageType") };
    CFStringRef values[] = { CFSTR("Developer") };
    CFDictionaryRef options = CFDictionaryCreate(NULL, (const void **)&keys, (const void **)&values, 1, &kCFTypeDictionaryKeyCallBacks, &kCFTypeDictionaryValueCallBacks);

    mach_error_t transfer_error = AMDeviceSecureTransferPath(0, device, url, options, (void*)&transfer_callback, 0);
    if (transfer_error) {
        printf("err=Unable to transfer package to device. (%x)\n", transfer_error);
        exit(1);
    }

    mach_error_t install_error = AMDeviceSecureInstallApplication(0, device, url, options, (void*)&install_callback, 0);
    if (install_error) {
        printf("err=Unable to install package. (%x)\n", install_error);
        exit(1);
    }

    CFRelease(path);
    CFRelease(options);

    //Extracting application bundle identifier from host app bundle and 
    //finding installation path on device by bundle identifier found on host
    if (!isIPA) 
    {
        CFBundleRef hostappBundle = CFBundleCreate(kCFAllocatorDefault, url);
        if(NULL != hostappBundle) {

            CFDictionaryRef hostappBundleDict;
            CFStringRef bundleName;
            char* bundleNameStrPtr;

            hostappBundleDict = CFBundleGetInfoDictionary( hostappBundle );
            
            if (NULL != hostappBundleDict) {

                bundleName = (CFStringRef)CFDictionaryGetValue(hostappBundleDict, CFSTR("CFBundleIdentifier"));

                if (NULL != bundleName)                                                 
                    bundleNameStrPtr = Copy_CFStringRefToCString( bundleName );
                else                                                                    
                    bundleNameStrPtr = NULL;                                            

            } else {
                printf("err=Unable to extract bundle name from app host bundle at %s\n", app_path);
            }

            if (NULL != bundleNameStrPtr) {
                if(!silent)
                    printf("Host app bundle identifier: %s\n", bundleNameStrPtr);

                //Finding installation path on device               
                CFDictionaryRef result;
                CFIndex dict_count,dict_index;
                CFTypeRef *theKeys;
                CFTypeRef *theValues;
                CFStringRef tCFStringRef;
                CFStringRef devicepath;
                CFStringRef apptype;
                CFStringRef devicebundleIdentifier;

                if (!lookup_applications(device, &result)) {
                   printf("err=Installed applications lookup failed\n");
                   exit(1);
                }

                dict_count = CFDictionaryGetCount(result);
                theKeys = (CFTypeRef*) NewPtrClear(sizeof(CFTypeRef*) * dict_count);
                theValues = (CFTypeRef*) NewPtrClear(sizeof(CFTypeRef*) * dict_count);
                if ((NULL != theKeys) && (NULL != theValues))
                {
                    CFDictionaryGetKeysAndValues(result,theKeys,theValues);
                    for (dict_index = 0;dict_index < dict_count;dict_index++)
                    {
                        char *keyStrPtr,*valueStrPtr,*devicepathStrPtr,*nullStrPtr = "<NULL>";

                        keyStrPtr = Copy_CFStringRefToCString((CFStringRef)theKeys[dict_index]);

                        tCFStringRef = CFCopyDescription(theValues[dict_index]);

                        apptype = (CFStringRef)CFDictionaryGetValue((CFDictionaryRef)theValues[dict_index], CFSTR("ApplicationType"));
                        devicebundleIdentifier = (CFStringRef)CFDictionaryGetValue((CFDictionaryRef)theValues[dict_index], CFSTR("CFBundleIdentifier"));

                        if ( (NULL != apptype) && (NULL != devicebundleIdentifier) && 
                             (CFStringCompare(apptype, CFSTR("User"), kCFCompareCaseInsensitive) == kCFCompareEqualTo) &&
                             (CFStringCompare(bundleName, devicebundleIdentifier, kCFCompareCaseInsensitive) == kCFCompareEqualTo)
                           )
                        {
                                devicepath = (CFStringRef)CFDictionaryGetValue((CFDictionaryRef)theValues[dict_index], CFSTR("Path"));
                                                                                                        
                                if (NULL != tCFStringRef)                                               
                                {                                                                       
                                    valueStrPtr = Copy_CFStringRefToCString(tCFStringRef);              
                                    CFRelease(tCFStringRef);                                            
                                }                                                                       
                                else                                                                    
                                    valueStrPtr = NULL;                                                 
                                                                                                        
                                if (NULL != devicepath)                                                 
                                    devicepathStrPtr = Copy_CFStringRefToCString(devicepath);           
                                else                                                                    
                                    devicepathStrPtr = NULL;                                            
                                                                                                        
                                if(!silent)
                                    printf("Path on device:\t %s\n", devicepathStrPtr ? devicepathStrPtr : nullStrPtr);                  
                                if (NULL != keyStrPtr) DisposePtr(keyStrPtr);                           
                                if (NULL != valueStrPtr) DisposePtr(valueStrPtr);                       
                                if (NULL != devicepathStrPtr) DisposePtr(devicepathStrPtr);             
                        } else {
                            //Skip System apps
                            continue;
                        }
                    }
                }
                else
                    printf("\n\t� Unable to allocate keys or values.");

                if (NULL != theKeys) DisposePtr((Ptr) theKeys);
                if (NULL != theValues) DisposePtr((Ptr) theValues);
                CFRelease(result);
                DisposePtr( bundleNameStrPtr );
            }             
            CFRelease( hostappBundle );

        } else {
            printf("err=Unable to extract bundle name from app host bundle at %s\n", app_path);
        }
    }

    if(!((AMDeviceStopSession(device) == 0) && (AMDeviceDisconnect(device) == 0))) {
       printf("err=Session stop failed\n");
       exit(1);
    } 

    if(!silent)
       printf("[100%%] Installed package %s\n", app_path);
    printf("err=Package has been installed successfully: %s\n", app_path);
    exit(0);
}

void uninstall_device_callback(struct am_device_notification_callback_info *info, void *arg) {
    switch (info->msg) {
        case ADNCI_MSG_CONNECTED:
            {
                if(physconntimeout != 0) //timeout was specified, device connected, so drop timer here
                    CFRunLoopTimerInvalidate(timer);

                CFStringRef keys[] = { CFSTR("PackageType") };
                CFStringRef values[] = { CFSTR("Developer") };
                CFDictionaryRef options = CFDictionaryCreate(NULL, (const void **)&keys, (const void **)&values, 1, &kCFTypeDictionaryKeyCallBacks, &kCFTypeDictionaryValueCallBacks);

                CFRetain(info->dev);

                CFStringRef found_device_id = AMDeviceCopyDeviceIdentifier(info->dev);

                if (found_device) 
                    return; // handle one device only
    
                if (device_id != NULL) {
                    char *found_device_id_StrPtr = Copy_CFStringRefToCString(found_device_id);
                
                    if((found_device_id_StrPtr !=NULL) && 
                       (strcmp(device_id, found_device_id_StrPtr) == 0)) {
                        found_device = true;
                        if(found_device_id_StrPtr !=NULL)
                          DisposePtr(found_device_id_StrPtr);
                    } else {
                        if(found_device_id_StrPtr !=NULL)
                          DisposePtr(found_device_id_StrPtr);
                        return;
                    }
                } else {
                    found_device = true;
                }

                AMDeviceConnect(info->dev);
                if (!(AMDeviceIsPaired(info->dev) && 
                     (AMDeviceValidatePairing(info->dev) == 0) &&
                     (AMDeviceStartSession(info->dev) == 0))) 
                {
                    printf("err=Can't start session with device. Please check if your Mac set as trusted computer on device.\n");
                    exit(1);
                }

                CFStringRef url = CFStringCreateWithCString(NULL, (const char *)app_path, kCFStringEncodingUTF8);
                mach_error_t uninstall_error = AMDeviceSecureUninstallApplication(0, info->dev, url, options, (void*)&install_callback, 0);
                if (uninstall_error) {
                    printf("err=Unable to uninstall package. (%x)\n", uninstall_error);
                    exit(1);
                }

                AMDeviceStopSession(info->dev);
                AMDeviceDisconnect(info->dev);

                CFRelease(options);
                printf("[100%%] %s package uninstalled.\n", app_path);
                exit(0);
            }
        default:
            break;
    }
}

void device_callback(struct am_device_notification_callback_info *info, void *arg) {
    switch (info->msg) {
        case ADNCI_MSG_CONNECTED:
            if(physconntimeout != 0) //timeout was specified, device connected, so drop timer here
                CFRunLoopTimerInvalidate(timer);
            handle_device(info->dev);
        default:
            break;
    }
}

/* Handler for Ctrl-C retranslation to forked GDB in manual debug mode */
pid_t childpid = -1;

void gdb_sigint_handler(int signum)
{
    kill(childpid, SIGINT);
}

void gdb_ready_handler(int signum)
{
    if (islauncherlldb && (lldb_socket_handle != -1)) 
    {
//     if(!silent)                                                                                  
//         printf("lldb socket shutdown\n");                                                      
       shutdown (lldb_socket_handle, SHUT_RDWR);
       close (lldb_socket_handle);
    }
    _exit(0);
}

void mount_callback(CFDictionaryRef dict, int arg);

void handle_rundebug(AMDeviceRef device) 
{
    CFStringRef appbundleIdentifier;
    CFURLRef appdevicepath;
    char *devicepathStrPtr;

    if (found_device) 
            return; // handle one device only
    
    CFStringRef found_device_id = AMDeviceCopyDeviceIdentifier(device);
    char *found_device_id_StrPtr = Copy_CFStringRefToCString(found_device_id);

    if (device_id != NULL) {
        if((found_device_id_StrPtr !=NULL) && 
           (strcmp(device_id, found_device_id_StrPtr) == 0)) {
            found_device = true;
        } else {
            if(NULL != found_device_id_StrPtr)
              DisposePtr(found_device_id_StrPtr);
            return;
        }
    } else {
        found_device = true;
        // save autodetected device UUID as ASCII string to global
        device_id = strdup(found_device_id_StrPtr);
    }

    CFRetain(device); // don't know if this is necessary?

    CFStringRef path = CFStringCreateWithCString(NULL, (const char*)app_path, kCFStringEncodingUTF8);
    CFURLRef relative_url = CFURLCreateWithFileSystemPath(NULL, path, kCFURLPOSIXPathStyle, false);
    CFURLRef url = CFURLCopyAbsoluteURL(relative_url);

    CFRelease(path);
    CFRelease(relative_url);

    CFStringRef keys[] = { CFSTR("PackageType") };
    CFStringRef values[] = { CFSTR("Developer") };
    CFDictionaryRef options = CFDictionaryCreate(NULL, (const void **)&keys, (const void **)&values, 1, &kCFTypeDictionaryKeyCallBacks, &kCFTypeDictionaryValueCallBacks);

    if(!silent)
        printf("[  0%%] Found device (%s), beginning install\n", found_device_id_StrPtr);

    AMDeviceConnect(device);
    if (!(AMDeviceIsPaired(device) && 
         (AMDeviceValidatePairing(device) == 0) &&
         (AMDeviceStartSession(device) == 0))) 
    {
        printf("err=Can't start session with device (UDID: %s). Please check if your Mac set as trusted computer on device.\n", 
               found_device_id_StrPtr);
        exit(1);
    }

    // NOTE: the secure version doesn't seem to require us to start the AFC service
    ServiceConnRef afcFd;
    AMDeviceSecureStartService(device, CFSTR("com.apple.afc"), NULL, &afcFd);
    AMDeviceStopSession(device);
    AMDeviceDisconnect(device);

    mach_error_t transfer_error = AMDeviceSecureTransferPath(0, device, url, options, (void*)&transfer_callback, 0);
    if (transfer_error) {
        printf("err=Unable to transfer package to device. (%x)\n", transfer_error);
        exit(1);
    }
    AMDServiceConnectionInvalidate(afcFd);

    AMDeviceConnect(device);
    if (!(AMDeviceIsPaired(device) && 
         (AMDeviceValidatePairing(device) == 0) &&
         (AMDeviceStartSession(device) == 0))) 
    {
        printf("err=Can't start session with device (UDID: %s). Please check if your Mac set as trusted computer on device.\n", 
               found_device_id_StrPtr);
        exit(1);
    }

    if(NULL != found_device_id_StrPtr)
      DisposePtr(found_device_id_StrPtr);

    mach_error_t install_error = AMDeviceSecureInstallApplication(0, device, url, options, (void*)&install_callback, 0);

    if (install_error) {
        printf("err=Unable to install package. (%x)\n", install_error);
        exit(1);
    }

    CFRelease(options);

    //Extracting application bundle identifier from host app bundle and 
    //finding installation path on device by bundle identifier found on host
    {
        CFBundleRef hostappBundle = CFBundleCreate(kCFAllocatorDefault, url);
        if(NULL != hostappBundle) {

            CFDictionaryRef hostappBundleDict;
            CFStringRef bundleName;
            char* bundleNameStrPtr;

            hostappBundleDict = CFBundleGetInfoDictionary( hostappBundle );
            
            if (NULL != hostappBundleDict) {

                bundleName = (CFStringRef)CFDictionaryGetValue(hostappBundleDict, CFSTR("CFBundleIdentifier"));

                if (NULL != bundleName)                                                 
                    bundleNameStrPtr = Copy_CFStringRefToCString( bundleName );
                else                                                                    
                    bundleNameStrPtr = NULL;                                            

            } else {
                printf("err=Unable to extract bundle name from app host bundle at %s\n", app_path);
            }

            if (NULL != bundleNameStrPtr) {
                if(!silent)
                    printf("Host app bundle identifier: %s\n", bundleNameStrPtr);
                //Finding installation path on device               
                CFDictionaryRef result;
                CFIndex dict_count,dict_index;
                CFTypeRef *theKeys;
                CFTypeRef *theValues;
                CFStringRef tCFStringRef;
                CFStringRef apptype;
                CFStringRef devicebundleIdentifier;
                CFStringRef devicepath;

                if (!lookup_applications(device, &result)) {
                   printf("err=Installed applications lookup failed\n");
                   exit(1);
                }

                dict_count = CFDictionaryGetCount(result);
                theKeys = (CFTypeRef*) NewPtrClear(sizeof(CFTypeRef*) * dict_count);
                theValues = (CFTypeRef*) NewPtrClear(sizeof(CFTypeRef*) * dict_count);
                if ((NULL != theKeys) && (NULL != theValues))
                {
                    CFDictionaryGetKeysAndValues(result,theKeys,theValues);
                    for (dict_index = 0;dict_index < dict_count;dict_index++)
                    {
//                      char *keyStrPtr,*valueStrPtr,*devicepathStrPtr,*nullStrPtr = "<NULL>";
                        char *keyStrPtr,*valueStrPtr,*nullStrPtr = "<NULL>";

                        keyStrPtr = Copy_CFStringRefToCString((const CFStringRef)theKeys[dict_index]);

                        tCFStringRef = CFCopyDescription(theValues[dict_index]);

                        apptype = (CFStringRef)CFDictionaryGetValue((CFDictionaryRef)theValues[dict_index], CFSTR("ApplicationType"));
                        devicebundleIdentifier = (CFStringRef)CFDictionaryGetValue((CFDictionaryRef)theValues[dict_index], CFSTR("CFBundleIdentifier"));

                        if ( (NULL != apptype) && (NULL != devicebundleIdentifier) && 
                             (CFStringCompare(apptype, CFSTR("User"), kCFCompareCaseInsensitive) == kCFCompareEqualTo) &&
                             (CFStringCompare(bundleName, devicebundleIdentifier, kCFCompareCaseInsensitive) == kCFCompareEqualTo)
                           )
                        {
                                appbundleIdentifier = devicebundleIdentifier;
                                devicepath = (CFStringRef)CFDictionaryGetValue((CFDictionaryRef)theValues[dict_index], CFSTR("Path"));
                                appdevicepath = CFURLCreateWithFileSystemPath(NULL, devicepath, kCFURLPOSIXPathStyle, true);
                                                                                                        
                                if (NULL != tCFStringRef)                                               
                                {                                                                       
                                    valueStrPtr = Copy_CFStringRefToCString(tCFStringRef);              
                                    CFRelease(tCFStringRef);                                            
                                }                                                                       
                                else                                                                    
                                    valueStrPtr = NULL;                                                 
                                                                                                        
                                if (NULL != devicepath)                                                 
                                    devicepathStrPtr = Copy_CFStringRefToCString(devicepath);           
                                else                                                                    
                                    devicepathStrPtr = NULL;                                            
                                if(!silent)
                                    printf("Path on device:\t %s\n",                                 
                                    devicepathStrPtr ? devicepathStrPtr : nullStrPtr);                  
                                if (NULL != keyStrPtr) DisposePtr(keyStrPtr);                           
                                if (NULL != valueStrPtr) DisposePtr(valueStrPtr);                       
//                              if (NULL != devicepathStrPtr) DisposePtr(devicepathStrPtr);             
                        } else {
                            //Skip System apps
                            continue;
                        }
                    }
                }
                else
                    printf("\n\t� Unable to allocate keys or values.");

                if (NULL != theKeys) DisposePtr((Ptr) theKeys);
                if (NULL != theValues) DisposePtr((Ptr) theValues);
                CFRelease(result);
                DisposePtr( bundleNameStrPtr );
            }             
            CFRelease( hostappBundle );

        } else {
            printf("Unable to extract bundle name from app host bundle at %s\n", app_path);
        }
    }

    if(!silent)
        printf("[100%%] Installed package %s\n", app_path);

    //Check if debugserver may be started without device support image remount
    dbgServiceConnection = NULL;
    CFStringRef serviceName = CFSTR("com.apple.debugserver");
    CFStringRef xkeys[] = { CFSTR("MinIPhoneVersion"), CFSTR("MinAppleTVVersion") };
    CFStringRef xvalues[] = { CFSTR("14.0"), CFSTR("14.0")};
    CFDictionaryRef version = CFDictionaryCreate(NULL, (const void **)&xkeys, (const void **)&xvalues, 2, &kCFTypeDictionaryKeyCallBacks, &kCFTypeDictionaryValueCallBacks);

    bool useSecureProxy = AMDeviceIsAtLeastVersionOnPlatform(device, version);
    if (useSecureProxy)
    {
        serviceName = CFSTR("com.apple.debugserver.DVTSecureSocketProxy");
    }

    if(AMDeviceSecureStartService(device, serviceName, NULL, &dbgServiceConnection) == 0) {
        sleep(1);
        assert(dbgServiceConnection != NULL);
        if (!useSecureProxy)
        {
            disable_ssl(dbgServiceConnection);
        }
        gdbfd = AMDServiceConnectionGetSocket(dbgServiceConnection);
        start_remote_debug_server(device);  // start debugserver
    } else {

        CFStringRef cfimage_path = CFStringCreateWithFormat(NULL, NULL, CFSTR("%@/DeveloperDiskImage.dmg"), copy_device_support_path(device, 1)); //Search for DMG only                                                                                       
        CFStringRef sig_path = CFStringCreateWithFormat(NULL, NULL, CFSTR("%@.signature"), cfimage_path);                                                                                       

        if(path_exists(cfimage_path, false) && path_exists(sig_path, false)) {
            FILE* sig = fopen(CFStringGetCStringPtr(sig_path, kCFStringEncodingMacRoman), "rb");                                                                                                                  
            void *sig_buf = malloc(128);                                                                                                                                                      
            assert(fread(sig_buf, 1, 128, sig) == 128);                                                                                                                                       
            fclose(sig);                                                                                                                                                                      
            CFDataRef sig_data = CFDataCreateWithBytesNoCopy(NULL, (const UInt8 *)sig_buf, 128, NULL);                                                                                                       
            CFRelease(sig_path);                                                                                                                                                              
                                                                                                                                                                                              
            CFTypeRef keys[] = { CFSTR("ImageSignature"), CFSTR("ImageType") };                                                                                                               
            CFTypeRef values[] = { sig_data, CFSTR("Developer") };                                                                                                                            
            CFDictionaryRef options = CFDictionaryCreate(NULL, (const void **)&keys, (const void **)&values, 2, &kCFTypeDictionaryKeyCallBacks, &kCFTypeDictionaryValueCallBacks);            
            CFRelease(sig_data);                                                                                                                                                              
                                                                                                                                                                                              
            int result = AMDeviceMountImage(device, cfimage_path, options, (void*)&mount_callback, 0);                                                                                                 
            CFRelease(options);
            CFRelease(cfimage_path);                                                                                                                                                                   
            if (result == 0) {                                                                                                                                                                
        if (!silent) 
                printf("[ 95%%] Developer disk image mounted successfully\n");                                                                                                                
            } else if (result == 0xe8000076 /* already mounted */) {                                                                                                                          
        if (!silent) 
                printf("[ 95%%] Developer disk image already mounted\n");                                                                                                                     
            } else if (result == 0xe8000033 /* different image already mounted */) {                                                                                                                          
            if (!silent) 
                        printf("[ 95%%] Warning: Image different to developer disk image found already mounted. Check images in DeviceSupport directory.\n");                                                                                                                     

            } else {                                                                                                                                                                          
                printf("err=Unable to mount developer disk image. (%x)\n", result);                                                                                                        
                exit(1);                                                                                                                                                                      
            }   

            //Retry debugserver start
            int start_err = AMDeviceSecureStartService(device, serviceName, NULL, &dbgServiceConnection);
            if (start_err != 0) {
                switch(start_err)
                {
                    case 0xe8000022:
                        sleep(2);
                        break;
                    case 0x800002d:
                        AMDeviceDisconnect(device);
                        AMDeviceConnect(device);
                        AMDeviceIsPaired(device);
                        AMDeviceValidatePairing(device);
                        AMDeviceStartSession(device);
                        break;
                   default:
                        start_err = -1;
               }
               if (start_err != -1)
                   start_err = AMDeviceSecureStartService(device, serviceName, NULL, &dbgServiceConnection);
            }

            if (start_err == 0) {
                 sleep(1);
                 assert(dbgServiceConnection != NULL);
                 if (!useSecureProxy)
                 {
                     disable_ssl(dbgServiceConnection);
                 }
                 gdbfd = AMDServiceConnectionGetSocket(dbgServiceConnection);
                 start_remote_debug_server(device);  // start debugserver
            } else {
                AMDeviceStopSession(device);
                AMDeviceDisconnect(device);
                printf("err=Can't start debugserver on device - device support image was not mounted.\n");
                exit(1);
            }                                                                                                                                                                              
        } else {
            AMDeviceStopSession(device);
            AMDeviceDisconnect(device);
            printf("err=Device support image or/and its signature is not reachable.\n");
            exit(1);                                                                                                                                                  
        }
    }

    if(debug || islauncherlldb) {

        if(!silent) {
            if(debug) {                                                                                         
                printf("Run with Debug\n");                                                           
                printf("App not started yet. Use run (CLI) or -exec-run (MI) command for start.\n");
            }
            else
                printf("Run without Debugging\n");                                                           
        }                                                           

		if(!islauncherlldb)                                                                                                             
	        write_gdb_prep_cmds(device, url, appbundleIdentifier, appdevicepath);
		else
	        write_lldb_prep_cmds(device, url, appdevicepath);                       
                                                                                                             
        CFRelease(url);                                                                                      
                                                                                                             
        if(!silent) {                                                                                        
            printf("[100%%] Connecting to remote debug server\n");                                           
        }                                                                                                    
                                                                                                             
        //Human user session or automated run ?                                                              
        if(launcher_path) {                                                              
            struct passwd *passwd;
            char preppathbuf[256];

            //get current user details
            passwd = getpwuid(getuid());

            //Launch GDB - user manual session                                                               
            signal(SIGHUP, gdb_ready_handler);                                                               
            signal(SIGINT, gdb_sigint_handler);                                                               
                                                                                                   
            pid_t parent = getpid();                                                                         
            childpid = fork();                                                                                
            if (childpid == 0) {                                                                                  
                char buf[4096];                                                                              
                CFStringRef cflauncher_path = CFStringCreateWithCString(NULL, (const char *)launcher_path, kCFStringEncodingUTF8);
                char *launcher_pathStr = Copy_CFStringRefToCString(cflauncher_path);

                sprintf(buf, "%s", launcher_pathStr);                                                           

                DisposePtr(launcher_pathStr);
                CFRelease(cflauncher_path);             

                int i;                                                                                       
                for(i=0;i<launcheroptcnt;i++)                                                                
                {                                                                                            
                    strcat(buf, " ");                                                                        
                    strcat(buf, launcher_options[i]);                                                        
                }                                                                                            
                strcat(buf, " ");                                                                            
                if (!islauncherlldb)
				{
                	strcat(buf, PREP_CMDS_PATH_WITH_X);
	                strcat(buf, "-");                                                                            
    	            strcat(buf, passwd->pw_name);                                                            
				}
    	        else
				{
                	strcat(buf, LLDB_PREP_CMDS_PATH_WITH_S);
	                strcat(buf, "-");                                                                            
    	            strcat(buf, passwd->pw_name);                                                            
				}
                if(!silent)                                                                                  
                    printf("call launcher: %s\n", buf);                                                      
                system(buf);      // launch gdb                                                              
                kill(parent, SIGHUP);   // "No. I am your father."                                           
                _exit(0);                                                                                    
            }                                                                                                
            printf("pid=0\n");
            fflush(stderr);
            fflush(stdout);
        } else {                                                                                             
            //if launcher not specified just print path to file with GDB prep commands and hang in RunLoop   
            printf("file=%s\n", prepbuf);                                                                    
            fflush(stdout);

            // Waiting for stdin input for target stop request for iosinstall standalone sessions.
            // Used by older paservers only, new paservers use target stop via iosgdb stop socket now.
            // Can cause CPU excessive consumption under paserver if enabled due to stdin polling.
            // add_stdin_runloop_callback();
        }                                                                                                    
    } else {
        //Run without debugging
        if(!silent)                                                                                          
            printf("Run without Debugging\n");                                                           

        //Write RSP commands directly to opened gdbfd
        char* cmds[] = {                                                                        
            "will be replaced with hex encoding of apppath",                                  
            "Hc0",                                                                            
            "c",                                                                              
            NULL                                                                              
        };                                                                                    

        if (NULL != devicepathStrPtr)  {                                                      
        cmds[0] = (char*)malloc(4096); // 4kb for app path and arguments max                                                              
        char* p = cmds[0];                                                                    

        sprintf(p, "A%d,0,", (int)strlen(devicepathStrPtr)*2); //apppath with argc
        p += strlen(p);                                                                       
        char* q = devicepathStrPtr;                                                           
        while (*q) {                                                                          
            *p++ = tohex(*q >> 4);                                                            
            *p++ = tohex(*q & 0xf);                                                           
            q++;                                                                              
        }                                                                                     
        *p = 0;                                                                               

        if (appargc > 0)
        {
          int count;
          for (count = 0; count < appargc; count++) {
            if(!silent)
                printf("warn=app argv[%d] = %s\n", count, appargv[count]);
            sprintf(p, ",%d,%d,", (int)strlen(appargv[count])*2, count+1); //apppath with argc
            p += strlen(p);                                                                       
            char* q = (char*)appargv[count];                                                           
            while (*q) {                                                                          
                *p++ = tohex(*q >> 4);                                                            
                *p++ = tohex(*q & 0xf);                                                           
                q++;                                                                              
            }                                                                                     
            *p = 0;                                                                               
          }
        }
                                  
        if(!silent)                                                                                          
            printf("App string to launch on device: %s\n", cmds[0]);                                                                                                                                                     
        DisposePtr(devicepathStrPtr);                                                         
                                                                                              
        char** cmd = cmds;                                                                    
        while (*cmd) {                                                                        
            if(!silent)                                                                       
                printf("'%s'\n", *cmd);                                                       
            send_pkt(*cmd, gdbfd);                                                            
            recv_pkt(gdbfd);                                                                  
            cmd++;                                                                            
        }                                                                                     
        
        printf("pid=0\n");
        fflush(stderr);
        fflush(stdout);

        //Read remote program output until fd will not closed.
        while (1)
            if ((recv_pkt(gdbfd) == 0) ||
                appthreadstopped) //connection closed on device or app got SIGKILL ?
                break;            //if so - exit loop.
        // Check if app not exited normally and kill it in this case
        if (appthreadstopped) 
        {
            //Write RSP commands directly to opened gdbfd
            char* cmds[] = {                                                                        
                "k",                                                                              
                NULL                                                                              
            };                                                                                    
            char** cmd = cmds;                                                                    
            while (*cmd) {                                                                        
                if(!silent)                                                                       
                    printf("'%s'\n", *cmd);                                                       
                send_pkt(*cmd, gdbfd);                                                            
                recv_pkt(gdbfd);                                                                  
                cmd++;                                                                            
            }                                                                                     
        }
        printf("err=Program has been finished.\n");
        close(gdbfd);
        exit(0);

    } else {
        printf("err=Can't find app path on device\n");
        exit(1);
    }
                                                                        
        
    } //Run Without Debugging
                                                                                
}

void rundebug_callback(struct am_device_notification_callback_info *info, void *arg) {
    switch (info->msg) {
        case ADNCI_MSG_CONNECTED:
            if(physconntimeout != 0) //timeout was specified, device connected, so drop timer here
                CFRunLoopTimerInvalidate(timer);
            handle_rundebug(info->dev);
        default:
            break;
    }
}

void listapps_device_callback(struct am_device_notification_callback_info *info, void *arg) {
    switch (info->msg) {
        case ADNCI_MSG_CONNECTED:
            {
                CFDictionaryRef result;
                CFIndex dict_count,dict_index;
                CFTypeRef *theKeys;
                CFTypeRef *theValues;
                CFStringRef tCFStringRef;
                CFStringRef devicepath;
                CFStringRef apptype;
        
                if(physconntimeout != 0) //timeout was specified, device connected, so drop timer here
                    CFRunLoopTimerInvalidate(timer);

                CFRetain(info->dev);

                CFStringRef found_device_id = AMDeviceCopyDeviceIdentifier(info->dev);
                AMDeviceConnect(info->dev);
                if (!(AMDeviceIsPaired(info->dev) && 
                     (AMDeviceValidatePairing(info->dev) == 0) &&
                     (AMDeviceStartSession(info->dev) == 0))) 
                {
                    printf("err=Can't start session with device. Please check if your Mac set as trusted computer on device.\n");
                    exit(1);
                }

                if (!lookup_applications(info->dev, &result)) {
                   printf("err=Installed applications lookup failed\n");
                   exit(1);
                }

                dict_count = CFDictionaryGetCount(result);
                printf("\n\tTotal app count installed on device: %ld\n",dict_count);

                theKeys = (CFTypeRef*) NewPtrClear(sizeof(CFTypeRef*) * dict_count);
                theValues = (CFTypeRef*) NewPtrClear(sizeof(CFTypeRef*) * dict_count);
                if ((NULL != theKeys) && (NULL != theValues))
                {
                    CFDictionaryGetKeysAndValues(result,theKeys,theValues);
                    for (dict_index = 0;dict_index < dict_count;dict_index++)
                    {
                        char *keyStrPtr,*valueStrPtr,*devicepathStrPtr,*nullStrPtr = "<NULL>";

                        keyStrPtr = Copy_CFStringRefToCString((CFStringRef)theKeys[dict_index]);

                        tCFStringRef = CFCopyDescription(theValues[dict_index]);

                        apptype = (CFStringRef)CFDictionaryGetValue((CFDictionaryRef)theValues[dict_index], CFSTR("ApplicationType"));

                        if ((NULL != apptype) && (CFStringCompare(apptype, CFSTR("User"), kCFCompareCaseInsensitive) == kCFCompareEqualTo))
                        {
                                devicepath = (CFStringRef)CFDictionaryGetValue((CFDictionaryRef)theValues[dict_index], CFSTR("Path"));
                                                                                                        
                                if (NULL != tCFStringRef)                                               
                                {                                                                       
                                    valueStrPtr = Copy_CFStringRefToCString(tCFStringRef);              
                                    CFRelease(tCFStringRef);                                            
                                }                                                                       
                                else                                                                    
                                    valueStrPtr = NULL;                                                 
                                                                                                        
                                if (NULL != devicepath)                                                 
                                    devicepathStrPtr = Copy_CFStringRefToCString(devicepath);           
                                else                                                                    
                                    devicepathStrPtr = NULL;                                            
                                                                                                        
//                              printf("\n\tkey & value #%ld are: \"%s\" and \"%s\".",                  
//                                  dict_index,                                                         
//                                  keyStrPtr ? keyStrPtr : nullStrPtr,                                 
//                                  valueStrPtr ? valueStrPtr : nullStrPtr);                            
//                              if (NULL != keyStrPtr) DisposePtr(keyStrPtr);                           
//                              if (NULL != valueStrPtr) DisposePtr(valueStrPtr);                       
                                                                                                        
                                printf("\n\t#%ld:\t%s, \t%s",                                           
                                    dict_index,                                                         
                                    keyStrPtr ? keyStrPtr : nullStrPtr,                                 
                                    devicepathStrPtr ? devicepathStrPtr : nullStrPtr);                  
                                if (NULL != keyStrPtr) DisposePtr(keyStrPtr);                           
                                if (NULL != valueStrPtr) DisposePtr(valueStrPtr);                       
                                if (NULL != devicepathStrPtr) DisposePtr(devicepathStrPtr);             
                        } else {
                            //Skip System apps
                            continue;
                        }
                    }
                    printf("\n");
                }
                else
                    printf("\n\t� Unable to allocate keys or values.");

                if (NULL != theKeys) DisposePtr((Ptr) theKeys);
                if (NULL != theValues) DisposePtr((Ptr) theValues);
                CFRelease(result);

                exit(0);
            }
        default:
            break;
    }
}

void mount_callback(CFDictionaryRef dict, int arg) {
    CFStringRef status = (CFStringRef)CFDictionaryGetValue(dict, CFSTR("Status"));

    if (CFEqual(status, CFSTR("LookingUpImage"))) {
    if (!silent) 
        printf("[  0%%] Looking up developer disk image\n");
    } else if (CFEqual(status, CFSTR("CopyingImage"))) {
    if (!silent) 
        printf("[ 30%%] Copying DeveloperDiskImage.dmg to device\n");
    } else if (CFEqual(status, CFSTR("MountingImage"))) {
    if (!silent) 
        printf("[ 90%%] Mounting developer disk image\n");
    }
}

void mount_device_callback(struct am_device_notification_callback_info *info, void *arg) {
    switch (info->msg) {
        case ADNCI_MSG_CONNECTED:
            {
                if(physconntimeout != 0) //timeout was specified, device connected, so drop timer here
                    CFRunLoopTimerInvalidate(timer);

                CFRetain(info->dev);

                CFStringRef found_device_id = AMDeviceCopyDeviceIdentifier(info->dev);
                AMDeviceRef device = info->dev;
                AMDeviceConnect(device);
                if (!(AMDeviceIsPaired(device) && 
                     (AMDeviceValidatePairing(device) == 0) &&
                     (AMDeviceStartSession(device) == 0))) 
                {
                    printf("err=Can't start session with device. Please check if your Mac set as trusted computer on device.\n");
                    exit(1);
                }

                version = AMDeviceCopyValue(device, 0, CFSTR("ProductVersion"));
                build = AMDeviceCopyValue(device, 0, CFSTR("BuildVersion"));
                char *versionStrPtr = Copy_CFStringRefToCString(version);
                char *buildStrPtr = Copy_CFStringRefToCString(build);
                if (!silent) {                                                                                                                                                                        
                    printf("Device data: %s (%s)\n", versionStrPtr, buildStrPtr );                                                                                                                                                  
                }
                DisposePtr(versionStrPtr);                                                                                                                                                                                     
                DisposePtr(buildStrPtr);                                                                                                                                                                                     

                CFStringRef cfimage_path = CFStringCreateWithCString(kCFAllocatorDefault, image_path, kCFStringEncodingMacRoman);                                                                                       
                CFStringRef sig_path = CFStringCreateWithFormat(NULL, NULL, CFSTR("%@.signature"), cfimage_path);                                                                                       

                if(path_exists(cfimage_path, false) && path_exists(sig_path, false)) {
                    FILE* sig = fopen(CFStringGetCStringPtr(sig_path, kCFStringEncodingMacRoman), "rb");                                                                                                                  
                    void *sig_buf = malloc(128);                                                                                                                                                      
                    assert(fread(sig_buf, 1, 128, sig) == 128);                                                                                                                                       
                    fclose(sig);                                                                                                                                                                      
                    CFDataRef sig_data = CFDataCreateWithBytesNoCopy(NULL, (const UInt8 *)sig_buf, 128, NULL);                                                                                                       
                    CFRelease(sig_path);                                                                                                                                                              
                                                                                                                                                                                                      
                    CFTypeRef keys[] = { CFSTR("ImageSignature"), CFSTR("ImageType") };                                                                                                               
                    CFTypeRef values[] = { sig_data, CFSTR("Developer") };                                                                                                                            
                    CFDictionaryRef options = CFDictionaryCreate(NULL, (const void **)&keys, (const void **)&values, 2, &kCFTypeDictionaryKeyCallBacks, &kCFTypeDictionaryValueCallBacks);            
                    CFRelease(sig_data);                                                                                                                                                              
                                                                                                                                                                                                      
                    int result = AMDeviceMountImage(device, cfimage_path, options, (void*)&mount_callback, 0);                                                                                                 
                    CFRelease(options);
                    CFRelease(cfimage_path);                                                                                                                                                                   
                    if (result == 0) {                                                                                                                                                                
            if (!silent) 
                        printf("[ 95%%] Developer disk image mounted successfully\n");                                                                                                                
                    } else if (result == 0xe8000076 /* already mounted */) {                                                                                                                          
            if (!silent) 
                        printf("[ 95%%] Developer disk image already mounted\n");                                                                                                                     
                    } else if (result == 0xe8000033 /* different image already mounted */) {                                                                                                                          
            if (!silent) 
                        printf("[ 95%%] Warning: Image different to developer disk image found already mounted. Check images in DeviceSupport directory.\n");                                                                                                                     
                    } else {                                                                                                                                                                          
                        printf("err=Unable to mount developer disk image. (%x)\n", result);                                                                                                        
                        exit(1);                                                                                                                                                                      
                    }                                                                                                                                                                                 
                } else {
                        printf("err=Device support image or/and its signature is not reachable.\n");
                        exit(1);                                                                                                                                                  
                }
                                                                                                                                                                                      
                AMDeviceStopSession(device);
                AMDeviceDisconnect(device);
                exit(0);
            }
        default:
            break;
    }
}

void viewdevices_device_callback(struct am_device_notification_callback_info *info, void *arg) {
    switch (info->msg) {
        case ADNCI_MSG_CONNECTED:
            {
                CFRetain(info->dev);

                CFStringRef found_device_id = AMDeviceCopyDeviceIdentifier(info->dev);
                AMDeviceRef device = info->dev;
                AMDeviceConnect(device);

                version = AMDeviceCopyValue(device, 0, CFSTR("ProductVersion"));
                build = AMDeviceCopyValue(device, 0, CFSTR("BuildVersion"));
                CFStringRef devicename = AMDeviceCopyValue(device, 0, CFSTR("DeviceName"));
                CFStringRef deviceclass = AMDeviceCopyValue(device, 0, CFSTR("DeviceClass"));
                CFStringRef hardwaremodel = AMDeviceCopyValue(device, 0, CFSTR("HardwareModel"));
                CFStringRef producttype = AMDeviceCopyValue(device, 0, CFSTR("ProductType"));
                char *versionStrPtr = Copy_CFStringRefToCString(version);
                char *buildStrPtr = Copy_CFStringRefToCString(build);
                char *UDIDStrPtr = Copy_CFStringRefToCString(found_device_id);
                char *devicenameStrPtr = Copy_CFStringRefToCString(devicename);
                char *deviceclassStrPtr = Copy_CFStringRefToCString(deviceclass);
                char *hardwaremodelStrPtr = Copy_CFStringRefToCString(hardwaremodel);
                char *producttypeStrPtr = Copy_CFStringRefToCString(producttype);
                printf("Discovered UDID: \"%s\" iOS: \"%s (%s)\" Name: \"%s\" DeviceClass: \"%s\" HardwareModel: \"%s\" ProductType: \"%s\"\n", 
                                                                      UDIDStrPtr, 
                                                                      versionStrPtr, 
                                                                      buildStrPtr, 
                                                                      devicenameStrPtr, 
                                                                      deviceclassStrPtr, 
                                                                      hardwaremodelStrPtr, 
                                                                      producttypeStrPtr 
                      );                                                                                                                                                  
                DisposePtr(versionStrPtr);                                                                                                                                                                                     
                DisposePtr(buildStrPtr);                                                                                                                                                                                     
                DisposePtr(UDIDStrPtr);                                                                                                                                                                                     
                DisposePtr(devicenameStrPtr);                                                                                                                                                                                     
                DisposePtr(deviceclassStrPtr);                                                                                                                                                                                                                                                                                                                                                                    
                DisposePtr(hardwaremodelStrPtr);                                                                                                                                                                                                                                                                                                                                                                    
                DisposePtr(producttypeStrPtr);                                                                                                                                                                                                                                                                                                                                                                    
                AMDeviceDisconnect(device);
            }
        case ADNCI_MSG_DISCONNECTED:
            {
                CFRetain(info->dev);

                CFStringRef found_device_id = AMDeviceCopyDeviceIdentifier(info->dev);
                AMDeviceRef device = info->dev;
                AMDeviceConnect(device);

                version = AMDeviceCopyValue(device, 0, CFSTR("ProductVersion"));
                build = AMDeviceCopyValue(device, 0, CFSTR("BuildVersion"));
                char *versionStrPtr = Copy_CFStringRefToCString(version);
                char *buildStrPtr = Copy_CFStringRefToCString(build);
                char *UDIDStrPtr = Copy_CFStringRefToCString(found_device_id);
                if (NULL == versionStrPtr) {                                                                                                                                                                        
                    printf("Disconnected UDID: \"%s\"\n", UDIDStrPtr);
                }                                                                                                                                                  
                DisposePtr(versionStrPtr);                                                                                                                                                                                     
                DisposePtr(buildStrPtr);                                                                                                                                                                                     
                DisposePtr(UDIDStrPtr);                                                                                                                                                                                                                                                                                                                                                                     
                AMDeviceDisconnect(device);
            }
        default:
            break;
    }
}


static void print_usage(int argc, char **argv)
{
    char *name = NULL;

    name = strrchr(argv[0], '/');
    printf("Usage: %s OPTIONS\n", (name ? name + 1 : argv[0]));
    printf("iOS Install tool.\n\n");
    printf
        ("  -U, --udid UDID\t\t\t\tTarget specific device by its 40-digit device UDID.\n"
         "  -r, --run PATH_TO_HOST_APP_BUNDLE\t\tRun (debug) app specified by host path.\n"
         "  -h, --help\t\t\t\t\tPrints usage information\n"
         "  -d, --debug\t\t\t\t\tEnable communication debugging with specified launcher\n" 
         "  -l, --list\t\t\t\t\tList apps currently installed on device\n" 
         "  -i, --install PATH_TO_HOST_APP_BUNDLE\t\tInstall application on iDevice\n" 
         "  -u, --uninstall BUNDLE_ID\t\t\tUninstall application on device by bundle ID\n" 
         "  -q, --quiet\t\t\t\t\tSilent mode for automated sessions\n" 
         "  -L, --launcher PATH_TO_LAUNCHER\t\tLauncher\n" 
         "  -o, --option 'optionN'\t\t\tAdditional option passed to launcher\n" 
         "  -x, --xcode MAJOR.MINOR\t\t\tExplicit XCode release setting, for example: 4.3 | 3.3 | 4.2 etc\n" 
         "  -m, --mount PATH_TO_DEBUG_IMAGE_DMG\t\tMount device support image\n" 
         "  -t, --timeout SECS\t\t\t\tDevice connection timeout (default - waiting forever)\n" 
         "  -p, --pass APPARG\t\t\t\tApplication argument\n" 
         "  -v, --view\t\t\t\t\tView attached devices (UDID)\n" 
         "  -a, --arch\t\t\t\t\tSet target architecture explicitly, armv7 set as default. For lldb launcher only.\n" 
         "  -n, --nextgen\t\t\t\t\tSetup debug session and output prep file path. For lldb only.\n" 
         "  -c, --customprepfile\t\t\t\tUser custom prep file. For lldb launcher mode only.\n" 
         "  -f, --forwardoutput\t\t\t\tForward app output to stdout in silent mode.\n"
        "\n");
}

static void parse_opts(int argc, char **argv)
{
    static struct option longopts[] = {
        {"help", 0, NULL, 'h'},
        {"uuid", 1, NULL, 'U'},
        {"run", 1, NULL, 'r'},
        {"debug", 0, NULL, 'd'},
        {"install", 1, NULL, 'i'},
        {"uninstall", 1, NULL, 'u'},
        {"list", 0, NULL, 'l'},
        {"quiet", 0, NULL, 'q'},
        {"launcher", 1, NULL, 'L'},
        {"option", 1, NULL, 'o'},
        {"xcode", 1, NULL, 'x'},
        {"mount", 1, NULL, 'm'},
        {"timeout", 1, NULL, 't'},
        {"pass", 1, NULL, 'p'},
        {"view", 0, NULL, 'v'},
        {"arch", 1, NULL, 'a'},
        {"nextgen", 0, NULL, 'n'},
        {"customprepfile", 1, NULL, 'c'},
        {"forwardoutput", 0, NULL, 'f'},
        {NULL, 0, NULL, 0}
    };
    int c;

    while (1) {
        c = getopt_long(argc, argv, "hU:r:di:u:lqL:o:x:m:t:p:va:nc:f", longopts, (int *) 0);
        if (c == -1) {
            break;
        }

        switch (c) {
        case 't':
			{
            	physconntimeout = atof(optarg);
			}
            break;
        case 'q':
			{
            	silent = true;
			}
            break;
        case 'f':
			{
            	forward = true;
			}
            break;
        case 'x':
			{
            	if(sscanf(optarg, "%d.%d", &xcodemajor, &xcodeminor) != 2) {
                	printf("warn=Xcode version specified in wrong format: MAJOR.MINOR. Will use first found on default paths.\n");
                	xcodemajor = xcodeminor = 0;
            	}
			}
            break;
        case 'L':
			{
            	launcher_path = wcsdup((wchar_t *)optarg);
            	CFStringRef cflauncher_path = CFStringCreateWithCString(NULL, (const char *)launcher_path, kCFStringEncodingUTF8);
            	if(!path_exists(cflauncher_path, false)) {
                	printf("err=Can't find specified Launcher executable.\n");
                	CFRelease(cflauncher_path);
                	exit(1);
            	} else {
                	CFRelease(cflauncher_path);             
            	}
			}
            break;
        case 'a':
           	target_arch = strdup(optarg);
            break;
        case 'n':
           	islauncherlldb = 1;
            break;
        case 'o':
            launcher_options[launcheroptcnt++] = strdup(optarg);
            if(!silent)
                printf("launcher option: %s\n", launcher_options[launcheroptcnt-1]);
            break;
        case 'm':
            op_mount = 1;
            image_path = strdup(optarg);
            chosen_callback = &mount_device_callback;
            break;
        case 'h':
            print_usage(argc, argv);
            exit(0);
        case 'U':
//            if (strlen(optarg) != 40) {
//                printf("err=invalid UDID specified (length != 40)\n");
//                print_usage(argc, argv);
//                exit(2);
//            }
            device_id = strdup(optarg);
            break;
        case 'r':
            op_run = 1;
            app_path = wcsdup((wchar_t *)optarg);
            chosen_callback = &rundebug_callback;
            break;
        case 'c':
            customprepfile_path = wcsdup((wchar_t *)optarg);
            break;
        case 'd':
            debug = true;
            break;
        case 'i':
            op_install = 1;
            app_path = wcsdup((wchar_t *)optarg);
            chosen_callback = &device_callback;
            break;
        case 'u':
            op_uninstall = 1;
            app_path = wcsdup((wchar_t *)optarg);
            chosen_callback = &uninstall_device_callback;
            break;
        case 'l':
            op_list = 1;
            chosen_callback = &listapps_device_callback;
            break;
        case 'p':
            if(appargc < (MAX_APP_ARGS-1)) {
                appargs[appargc] = strdup(optarg);
                appargc++;
                appargs[appargc] = NULL;
            }
            break;
        case 'v':
            op_view = 1;
            chosen_callback = &viewdevices_device_callback;
            break;
        default:
            print_usage(argc, argv);
            exit(2);
        }
    }

    if (optind <= 1 || (argc - optind > 0)) {
        print_usage(argc, argv);
        exit(2);
    }
}

int juststarted = 1;

//Timeout callbacks
static void _perform(void *info __unused)
{
    if(juststarted) {
        juststarted = 0;
    } else {
        if(!op_view) {
            printf("err=Device connection timeout\n");
            exit(2);
        } else {
           if(!silent)
              printf("warn=Devices discovery timeout\n");
           exit(0);
        }
    }
}

static void _timer(CFRunLoopTimerRef timer __unused, void* info)
{
    CFRunLoopSourceSignal((CFRunLoopSourceRef)info);
}

int main(int argc, char *argv[]) 
{
    // Disable output streams buffering
    setbuf(stdout, NULL);
    setbuf(stderr, NULL);

    // Checking parameters...
    parse_opts(argc, argv);

    argc -= optind;
    argv += optind;

    appargv = appargs;

    if((op_uninstall+op_run+op_install+op_list+op_mount+op_view) > 1) {
        printf("err=Only one operation per call allowed.\n");
        exit(2);
    }   

    if((debug || op_run || op_install) && !app_path) {
        printf("err=Application path required.\n");
        exit(2);
    }   

    if((!op_uninstall && !op_list && !op_mount && !op_view)) {

        if(!app_path) {
            printf("err=Application or IPA path required.\n");
            exit(2);
        }

        //Convert Bundle or IPA path to string object
        CFStringRef path = CFStringCreateWithCString(NULL, (const char *)app_path, kCFStringEncodingUTF8);

        // Check if install requested and IPA package specified instead of app bundle
        if( debug || op_run || op_install)
        {
            {
                // Check file type with "file" command - expect "Zip archive data", not "directory"
                // Create a file check task
                NSAutoreleasePool * pool = [[NSAutoreleasePool alloc] init];
                NSTask* fileCheckTask = [[[NSTask alloc] init] autorelease];
                [fileCheckTask setLaunchPath:@"/usr/bin/file"];
                [fileCheckTask setArguments:[NSArray arrayWithObject:(NSString*)path]];
                
                NSPipe* fileCheckPipe = [NSPipe pipe];
                id SavedStandardOutput = [fileCheckTask standardOutput];
                [fileCheckTask setStandardOutput:fileCheckPipe];
                NSFileHandle* fileCheckFile = [fileCheckPipe fileHandleForReading];
                
                [fileCheckTask launch];
                NSData* fileCheckData = [fileCheckFile readDataToEndOfFile];
                // We run known tool (file) with determined behavior, so can wait until run finished.
                [fileCheckTask waitUntilExit];
                
                NSString* fileCheckOutput =
                [[[NSString alloc] initWithData:fileCheckData
                                       encoding:NSUTF8StringEncoding] autorelease];
                fileCheckOutput = [fileCheckOutput stringByTrimmingCharactersInSet:
                          [NSCharacterSet whitespaceAndNewlineCharacterSet]];
                if ([fileCheckOutput length] == 0) {
                    if(!silent)
                        printf("warn=Can't detect specified app package type, assuming usual bundle.\n");
                }
                else {
                   isIPA = ([fileCheckOutput rangeOfString:@"Zip archive data" options:NSCaseInsensitiveSearch].location == NSNotFound) ? 0:1;
                }
                [pool release];
            }

            if (isIPA) { 
               if(!silent)
                  printf("warn=IPA package detected.\n"); 

                if(debug || op_run || !op_install) {
                    printf("err=Can't run or debug app specified as IPA distribution package. Installation only possible.\n");
                    exit(2);
                }   
                // Skip bundle checks - IPA installed as is
                goto myipa;
            }
            else { 
               if(!silent)
                  printf("warn=Developer app bundle detected.\n");
            }

        } // IPA ?

        // Bundle or IPA should exists on fs, continue with checking if it just file, not dir...
        if (!path_exists(path, true)) {
            printf("err=Application bundle argument is not bundle directory.\n");                                                                                                                                                       
            exit(2);
        } else {
            //Bundle directory check passed 
            //Check Info.plist presence inside app bundle
            CFMutableArrayRef filename_arr = CFArrayCreateMutable(kCFAllocatorDefault, 0, &kCFTypeArrayCallBacks);
            CFArrayAppendValue(filename_arr, path);
            CFArrayAppendValue(filename_arr, CFSTR("Info.plist"));
            path = CFStringCreateByCombiningStrings(kCFAllocatorDefault, filename_arr, CFSTR("/"));
            if (!path_exists(path, false)) {
                printf("err=Application bundle should have Info.plist inside.\n");                                                                                                                                                          
                exit(2);
            } else {
                //Info.plist presence check passed
                CFRelease(path);

                //Continue with inspecting bundle executable
                path = CFStringCreateWithCString(NULL, (const char *)app_path, kCFStringEncodingUTF8);
                CFURLRef appbundlesurl = CFURLCreateWithFileSystemPath(NULL, path, kCFURLPOSIXPathStyle, true);
                CFRelease(path);

                //Extract bundle exe info from app bundle
                CFBundleRef appBundle = CFBundleCreate(kCFAllocatorDefault, appbundlesurl);
                if(NULL != appBundle) {
                    CFURLRef appbundleexeurl = CFBundleCopyExecutableURL(appBundle);
                    if (NULL != appbundleexeurl) {                                                
                        if (CFURLResourceIsReachable ( appbundleexeurl, NULL )) {
                            //Application exe reachable
                            char appexePath[1024];

                            if (CFURLGetFileSystemRepresentation(appbundleexeurl, true, (UInt8 *)appexePath, sizeof(appexePath))) 
                            {                                                
                                if(!silent)
                                    printf("warn=Application bundle executable: %s\n", appexePath);
                            }
                            else {                                                                   
                                    CFRelease(appBundle);                                            
                                    printf("err=Unable to map application bundle executable url on FS representation\n");
                                    exit(2);
                            }

                            app_bundleID = CFBundleGetIdentifier(appBundle);

                            if (NULL != app_bundleID) {
                                char* srcbundleIDStrPtr;                                              
                                srcbundleIDStrPtr = Copy_CFStringRefToCString( app_bundleID );
                                if(!silent)
                                    printf("warn=Bundle ID: %s\n", srcbundleIDStrPtr);
                                //DisposePtr( srcbundleIDStrPtr );
                            } else  {                                                                   
                                printf("err=Unable to extract bundle ID from app bundle at %s\n", app_path);
                                exit(2);
                            }

                            CFRelease(appBundle);                                            
                        }
                        else {
                            CFRelease(appBundle);                                            
                            printf("err=Application executable specified in bundle Info.plist CFBundleExecutable key is not reachable\n");
                            exit(2);
                        }

                    }
                    else  {                                                                   
                        CFRelease(appBundle);                                            
                        printf("err=Unable to extract application bundle executable info. Please check Info.plist CFBundleExecutable key.\n");
                        exit(2);
                    }
                } else {
                    //BundleRef creation failed, exit
                    printf("err=Can't check bundle info for application bundle at specified path.\n");                                                                                                                                                          
                    exit(2);
                }                           
            }
        }
    
    }

myipa:

    if(getenv("IOSTIMEOUT") != NULL)
        physconntimeout = atof(getenv("IOSTIMEOUT"));                                                                                                           

    //Preparing timer for phys conn timeout
    if(!physconntimeout && !op_view) {
        if(!silent)
            printf("warn=Device connection timeout was not specified, will wait forever until device connected\n");                                                                       
    } else {
        bzero(&source_context, sizeof(source_context));
        source_context.perform = _perform;
        source = CFRunLoopSourceCreate(NULL, 0, &source_context);
        CFRunLoopAddSource(CFRunLoopGetCurrent(), source, kCFRunLoopCommonModes);

        bzero(&timer_context, sizeof(timer_context));
        timer_context.info = source;
        timer = CFRunLoopTimerCreate(kCFAllocatorDefault, CFAbsoluteTimeGetCurrent(), physconntimeout, 0, 0, _timer, &timer_context);
        CFRunLoopAddTimer(CFRunLoopGetCurrent(), timer, kCFRunLoopCommonModes);
    }

    //Xcode selected path
    memset(xcpath, 0, sizeof(xcpath));

    //Open xcselect library
    void* lib_handle = dlopen("/usr/lib/libxcselect.dylib", RTLD_LOCAL|RTLD_LAZY);
    if (!lib_handle) {
        if(!silent)
            printf("warn=Can't get Xcode selected installation path with method 1. Please check Xcode selected install path with xcode-select tool.\n");                                                                                                                                                          
    } else {
        //Resolve required function in xcselect library
        int (*get_developer_path)(char*, int, char*, char*, char*) = (int (*)(char*, int, char*, char*, char*))dlsym(lib_handle, "xcselect_get_developer_dir_path");
        if (!get_developer_path) {
            if(!silent)
                printf("warn=Can't get Xcode selected installation path with method 1. Please check Xcode selected install path with xcode-select tool.\n");                                                                                                                                                          
        } else {
            //Get Xcode selected path via xcselect lib getter function
            if( get_developer_path(&xcpath[2], sizeof(xcpath), xcpath, &xcpath[1], xcpath) == 1) {     
                if(!silent)
                    printf("Discovered Xcode path with method 1: %s\n", &xcpath[2]);
                xcode_found_via_xclib = 1;
            }
            else {
                if(!silent)
                    printf("warn=Can't get Xcode selected installation path with method 1. Please check Xcode selected install path with xcode-select tool.\n");                                                                                                                                                          
            }
            // Close xcselect library
            if (dlclose(lib_handle) != 0) {
                if(!silent)
                    printf("warn=Can't get Xcode selected installation path with method 1. Please check Xcode selected install path with xcode-select tool.\n");                                                                                                                                                          
                xcode_found_via_xclib = 0;
            }
        }
    }

    if (!xcode_found_via_xclib) {
        // Looks like Mountain Lion installed or earlier OSX version
        NSAutoreleasePool * pool = [[NSAutoreleasePool alloc] init];
        NSTask* GetXcodeDirTask = [[[NSTask alloc] init] autorelease];
        [GetXcodeDirTask setLaunchPath:@"/usr/bin/xcode-select"];
        [GetXcodeDirTask setArguments:[NSArray arrayWithObject:@"-print-path"]];
        
        NSPipe* GetXcodeDirPipe = [NSPipe pipe];
        id SavedStandardOutput = [GetXcodeDirTask standardOutput];
        [GetXcodeDirTask setStandardOutput:GetXcodeDirPipe];
        NSFileHandle* GetXcodeDirFile = [GetXcodeDirPipe fileHandleForReading];
        
        [GetXcodeDirTask launch];
        NSData* GetXcodeDirData = [GetXcodeDirFile readDataToEndOfFile];
//      We run known tool (xcode-select) with determined behavior, so can wait until run finished.
//        [GetXcodeDirTask terminate];
        [GetXcodeDirTask waitUntilExit];
        
        NSString* GetXcodeDirOutput =
        [[[NSString alloc] initWithData:GetXcodeDirData
                               encoding:NSUTF8StringEncoding] autorelease];
        GetXcodeDirOutput = [GetXcodeDirOutput stringByTrimmingCharactersInSet:
                  [NSCharacterSet whitespaceAndNewlineCharacterSet]];
        if ([GetXcodeDirOutput length] == 0) {
            if(!silent)
                printf("warn=Can't get Xcode selected installation path with method 2. Please check Xcode installation on your Mac. Fallback: default path /Applications/XCode.app...\n");                                                                                                                                                          
            xcode_found_via_xclib = 1;
            strcpy(&xcpath[2],"/Applications/Xcode.app/Contents/Developer");
        }
        else {
           memset(xcpath, 0, sizeof(xcpath));
           strcpy(&xcpath[2],[GetXcodeDirOutput cStringUsingEncoding: NSASCIIStringEncoding]);
           if(!silent)
                printf("Discovered Xcode path with method 2: %s\n", &xcpath[2]);
           xcode_found_via_xclib = 1;         
        }
        [pool release];
    }

    AMDSetLogLevel(5); // Set log level to required enough

    if(!silent)
        printf("Lookup for connected device...\n");

    AMDeviceNotificationSubscribe(chosen_callback, 0, 0, NULL, &notify); 

    CFRunLoopRun();
}
