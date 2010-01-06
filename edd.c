/* ppacket. Detect DDOS thru entropy
 *
 * Author: comotion@users.sf.net
 * Idea by breno.silva@gmail.com
 http://lists.openinfosecfoundation.org/pipermail/oisf-wg-portscan/2009-October/000023.html
 * Thanks to ebf0 (http://www.gamelinux.org/) whose support code is good enough.
 * License? If U have the code U have the GPL... >:-P

Entropy  H(P1) + H(P2) + ... + H(Pi) > H(P1P2..Pi) => DDOS


Pseudo code:
   # can segment into destport or src:port:dst:port
   for each packet
      count set bits
      count packet bits
      sum_entropy = Entropy(packet);
      track window of n last packets{
         increase set & total bit values
         if(H(window) > H(p1p2..pwin)
            => DDOS!
      }

 */


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <netinet/in.h> 
#include <signal.h>
#include <pcap.h>
#include <getopt.h>
#include <time.h>
#include <sys/types.h>
#include <grp.h>
#include <pwd.h>
#include <unistd.h>
#include <sys/stat.h>
#include <syslog.h>
#include <fcntl.h>
#include <errno.h>
#include <limits.h>
#include <math.h>
#include "edd.h"

static int   verbose, inpacket, intr_flag, use_syslog;

time_t       timecnt,tstamp;
pcap_t       *handle;
static char  *dev,*dpath,*chroot_dir;
static char  *group_name, *user_name, *true_pid_name;
static char  *pidfile = "edd.pid";
static char  *pidpath = "/var/run";
static int   verbose, inpacket, intr_flag, use_syslog;


/* our window of packets */
#define P_WINDOW 0xFF // 256
static uint32_t p_set[P_WINDOW];
static uint32_t p_tot[P_WINDOW];
static double  p_entropy[P_WINDOW];
static uint32_t head = 0, tail = 0;
static uint32_t b_tot = 0, b_set = 0;

void game_over() {
   fprintf(stderr, "it is over my friend\n");
   if ( inpacket == 0 ) {
      pcap_close(handle);
      exit (0);
   }
   intr_flag = 1;
}

/* For each byte, for each bit: count bits. Kernighan style */
inline uint32_t count_bits(const u_char *packet, const uint32_t p_len)
{
   const uint32_t *ptr = (uint32_t *) packet;
   const uint32_t *end = (uint32_t *) (packet + p_len);
   uint32_t v; // count the number of bits set in v
   uint8_t  c; // c accumulates the total bits set in v
   uint32_t set_bits = 0;
   while (ptr < end){
      v = *ptr++;
      for (c = 0; v; c++) {
         v &= v - 1; // clear the least significant bit set
      }
      set_bits += c;
   }
   return set_bits;
}

/* count bits in parallel
 * How? With magick bit patterns. 
 * Thx go to http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel
 * The B array, expressed as binary, is:
       0x1235467A = 01110101 00010010 10001010 11101101
B[0] = 0x55555555 = 01010101 01010101 01010101 01010101
B[1] = 0x33333333 = 00110011 00110011 00110011 00110011
B[2] = 0x0F0F0F0F = 00001111 00001111 00001111 00001111
B[3] = 0x00FF00FF = 00000000 11111111 00000000 11111111
B[4] = 0x0000FFFF = 00000000 00000000 11111111 11111111
                                                      
We can adjust the method for larger integer sizes by continuing with the patterns for the Binary Magic Numbers, B and S. If there are k bits, then we need the arrays S and B to be ceil(lg(k)) elements long, and we must compute the same number of expressions for c as S or B are long. For a 32-bit v, 16 operations are used.
 */
inline uint32_t count_bits_p(const u_char *packet, const uint32_t p_len)
{
   uint32_t v, c, set_bits = 0;
   static const int S[] = { 1, 2, 4, 8, 16}; 
   static const int B[] = {0x55555555, 0x33333333, 0x0F0F0F0F, 0x00FF00FF, 0x0000FFFF};
   
   const uint32_t *ptr = (uint32_t *) packet;
   const uint32_t *end = (uint32_t *) (packet + p_len);
   while(end > ptr){
      v = *ptr++;
      c = v - ((v >> 1) & B[0]);
      c = ((c >> S[1]) & B[1]) + (c & B[1]);
      c = ((c >> S[2]) + c) & B[2];
      c = ((c >> S[3]) + c) & B[3];
      c = ((c >> S[4]) + c) & B[4];
      set_bits += c;
   }
   return set_bits;
}

/* this algo does 4 bytes at a time. Note! what about garbage padding? */
uint32_t count_bits_pp(const u_char *packet, const uint32_t p_len)
{
   uint32_t v, set_bits = 0;
   const uint32_t *ptr = (uint32_t *) packet;
   const uint32_t *end = (uint32_t *) (packet + p_len);

   while(end > ptr){
      v = *ptr++;
      //fprintf(stderr, "%08p ", v);
      v = v - ((v >> 1) & 0x55555555);                    // reuse input as temporary
      v = (v & 0x33333333) + ((v >> 2) & 0x33333333);     // temp
      set_bits += ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24; // count
   }
   /* last N<4 bytes */
   //uint8_t mod = p_len % 4;
   //set_bits += count_bits((uint8_t*)ptr,p_len % 4);
   //fprintf(stderr, "\n");
   return set_bits;
}

/* same dog, except use 64bit datatype*/
uint32_t count_bits_64(const u_char *packet, const uint32_t p_len)
{
   uint64_t v, set_bits = 0;
   const uint64_t *ptr = (uint64_t *) packet;
   const uint64_t *end = (uint64_t *) (packet + p_len);

   while(end > ptr){
      v = *ptr++;
      //fprintf(stderr, "%08p ", v);
      v = v - ((v >> 1) & 0x5555555555555555);                    // reuse input as temporary
      v = (v & 0x3333333333333333) + ((v >> 2) & 0x3333333333333333);     // temp
      v = (v + (v >> 4)) & 0x0F0F0F0F0F0F0F0F;
      set_bits += (v * 0x0101010101010101) >> (sizeof(v) - 1) * CHAR_BIT; // count
   }
   //set_bits += count_bits_p((uint8_t *)ptr, p_len % 4);
   //fprintf(stderr, "\n");
   return set_bits;
}

   /* this can be generalized if we have a 64bit or 128 bit type T
      v = v - ((v >> 1) & (T)~(T)0/3);                           // temp
      v = (v & (T)~(T)0/15*3) + ((v >> 2) & (T)~(T)0/15*3);      // temp
      v = (v + (v >> 4)) & (T)~(T)0/255*15;                      // temp
      c = (T)(v * ((T)~(T)0/255)) >> (sizeof(v) - 1) * CHAR_BIT; // count
    */

/* simplistic bit-by-bit implementation */
inline uint32_t count_bits_kw(const u_char *packet, const uint32_t p_len)
{
   uint32_t tmp;
   uint32_t set_bits = 0;
   // byte for byte
   const u_char *ptr = packet;
   while(ptr != packet + p_len){
      tmp = *ptr;
      while(tmp){
         // isolate bit
         set_bits += tmp & 0x1;
         tmp >>= 1;
      }
      ptr++;
   }
   return set_bits;
}


/* count bits by lookup table */
static const unsigned char BitsSetTable256[256] = 
{
#   define B2(n) n,     n+1,     n+1,     n+2
#   define B4(n) B2(n), B2(n+1), B2(n+1), B2(n+2)
#   define B6(n) B4(n), B4(n+1), B4(n+1), B4(n+2)
    B6(0), B6(1), B6(1), B6(2)
};
    /*
    // To initially generate the table algorithmically:
    BitsSetTable256[0] = 0;
    for (int i = 0; i < 256; i++)
    {
      BitsSetTable256[i] = (i & 1) + BitsSetTable256[i / 2];
    }
    */


inline uint32_t count_bits_t1(const u_char *packet, const uint32_t p_len){

   uint32_t v, set_bits = 0;
   const uint32_t *ptr = (uint32_t *) packet;
   const uint32_t *end = (uint32_t *) (packet + p_len);

   while(end >= ptr){
        v = *ptr++; // count the number of bits set in 32-bit value v

        // Option 1:
        set_bits += BitsSetTable256[v & 0xff] +
            BitsSetTable256[(v >> 8) & 0xff] + 
            BitsSetTable256[(v >> 16) & 0xff] + 
            BitsSetTable256[v >> 24]; 
   }
   return set_bits;
}

inline uint32_t count_bits_t2(const u_char *packet, const uint32_t p_len){

   uint32_t v, set_bits = 0;
   const uint32_t *ptr = (uint32_t *) packet;
   const uint32_t *end = (uint32_t *) (packet + p_len);
   unsigned char *p;

   while(end >= ptr){
        v = *ptr++; // count the number of bits set in 32-bit value v
        //unsigned int c; // c is the total bits set in v

        // Option 2:
        p = (unsigned char *) &v;
        set_bits += BitsSetTable256[p[0]] + 
            BitsSetTable256[p[1]] + 
            BitsSetTable256[p[2]] +	
            BitsSetTable256[p[3]];
   }
   return set_bits;
}

/* Could do algo selection based on best performance */
void packet_profiler (const u_char *packet, const uint32_t p_len)
{
   uint64_t s, e;
   const uint32_t p_bits = p_len*8;
   __asm__ __volatile__("cpuid: rdtsc;" : "=A" (s) :: "ebx", "ecx", "memory");
   uint32_t set_bits = count_bits_pp(packet, p_len);
   __asm__ volatile("rdtsc":"=A"(e));
   //printf("S: %llu\nD: %llu\ndiff: %lld\n", s, e, e - s);
   printf("[PP] [%lld] Bytes: %lu, Bits: %lu, Set: %lu\n", e - s,
          p_len, p_bits, set_bits);
   
   __asm__ volatile("rdtsc":"=A"(s));
   set_bits = count_bits_64(packet, p_len);
   __asm__ volatile("rdtsc":"=A"(e));
   printf("[64] [%lld] Bytes: %lu, Bits: %lu, Set: %lu\n", e - s,
          p_len, p_bits, set_bits);

   __asm__ volatile("rdtsc":"=A"(s));
   set_bits = count_bits_t1(packet, p_len);
   __asm__ volatile("rdtsc":"=A"(e));
   printf("[T1] [%lld] Bytes: %lu, Bits: %lu, Set: %lu\n", e - s,
          p_len, p_bits, set_bits);

   __asm__ volatile("rdtsc":"=A"(s));
   set_bits = count_bits_t2(packet, p_len);
   __asm__ volatile("rdtsc":"=A"(e));
   printf("[T2] [%lld] Bytes: %lu, Bits: %lu, Set: %lu\n", e - s,
          p_len, p_bits, set_bits);

   __asm__ volatile("rdtsc":"=A"(s));
   set_bits = count_bits_p(packet, p_len);
   __asm__ volatile("rdtsc":"=A"(e));
   printf("[ P] [%lld] Bytes: %lu, Bits: %lu, Set: %lu\n", e - s,
          p_len, p_bits, set_bits);

   __asm__ volatile("rdtsc":"=A"(s));
   set_bits = count_bits(packet, p_len);
   __asm__ volatile("rdtsc":"=A"(e));
   printf("[KR] [%lld] Bytes: %lu, Bits: %lu, Set: %lu\n", e - s,
          p_len, p_bits, set_bits);

   __asm__ volatile("rdtsc":"=A"(s));
   set_bits = count_bits_kw(packet, p_len);
   __asm__ volatile("rdtsc":"=A"(e));
   printf("[KW] [%lld] Bytes: %lu, Bits: %lu, Set: %lu\n", e - s,
          p_len, p_bits, set_bits);
}

/* calculate the simple entropy of a packet, ie
 * assume all bits are equiprobable and randomly distributed
 *
 * needs work: do this with pure, positive ints?
 * tresholds? markov chains? averaging?
 * 
 * check this with our friend the kolmogorov
 */

double simple_entropy(double set_bits, double total_bits)
{
    return total_bits * (( -set_bits / total_bits )*log2(set_bits/total_bits)
            - (1 - (set_bits / total_bits) * log2(1 - (set_bits/total_bits))))
            + log2(total_bits);
}

static uint32_t packet_count;

void got_packet (u_char *useless,const struct pcap_pkthdr *pheader, const u_char *packet)
{
   if ( intr_flag != 0 ) { game_over(); }
   inpacket = 1;
   tstamp = time(NULL);
   const uint32_t p_len = ((pheader->len > SNAPLENGTH)?SNAPLENGTH:pheader->len);
   const uint32_t bits = p_len*8;
   uint32_t set = count_bits_64(packet, p_len);
   static const double tresh = 100;

   p_tot[head] = bits;
   p_set[head] = set;
   p_entropy[head] = simple_entropy(set, bits);

   packet_count++;
   if (packet_count < P_WINDOW) {
       printf("[%lu] %lu/%lu, E(%f)\n", head, set, bits, p_entropy[head]);
   } else {
       // we have some packets for analysis
       uint32_t k, total_set = 0, total_bits = 0;
       double sum_entropy = 0;
       for(k = 0; k < P_WINDOW; k++){
           total_set += p_set[k];
           total_bits+= p_tot[k];
           sum_entropy += p_entropy[k];
       }
       double joint_entropy = simple_entropy(total_set, total_bits);
       if(tresh < sum_entropy - joint_entropy ){
           fprintf(stderr, "ddos attack!!! e(%f) < te(%f)\n", 
                   joint_entropy, sum_entropy);
       }else{
           fprintf(stdout, "no news, e(%f) >= te(%f)\n", 
                   joint_entropy, sum_entropy);
       }
   }

   head = (head + 1) % P_WINDOW;


   ether_header *eth_hdr;
   eth_hdr = (ether_header *) (packet);
   u_short eth_type;
   eth_type = ntohs(eth_hdr->eth_ip_type);
   int eth_header_len;
   eth_header_len = ETHERNET_HEADER_LEN;

   /* sample code from cxtracker

   u_short p_bytes;
   if ( eth_type == ETHERNET_TYPE_8021Q ) {
      // printf("[*] ETHERNET TYPE 8021Q\n");
      eth_type = ntohs(eth_hdr->eth_8_ip_type); 
      eth_header_len +=4;
   }

   else if ( eth_type == (ETHERNET_TYPE_802Q1MT|ETHERNET_TYPE_802Q1MT2|ETHERNET_TYPE_802Q1MT3|ETHERNET_TYPE_8021AD) ) {
      // printf("[*] ETHERNET TYPE 802Q1MT\n");
      eth_type = ntohs(eth_hdr->eth_82_ip_type);
      eth_header_len +=8;
   }

   if ( eth_type == ETHERNET_TYPE_IP ) {
      // printf("[*] Got IPv4 Packet...\n");
      ip4_header *ip4;
      ip4 = (ip4_header *) (packet + eth_header_len);
      p_bytes = (ip4->ip_len - (IP_HL(ip4)*4));
      struct in6_addr ip_src, ip_dst;
      ip_src.s6_addr32[0] = ip4->ip_src;
      ip_src.s6_addr32[1] = 0;
      ip_src.s6_addr32[2] = 0;
      ip_src.s6_addr32[3] = 0;
      ip_dst.s6_addr32[0] = ip4->ip_dst;
      ip_dst.s6_addr32[1] = 0;
      ip_dst.s6_addr32[2] = 0;
      ip_dst.s6_addr32[3] = 0;

      if ( ip4->ip_p == IP_PROTO_TCP ) {
         tcp_header *tcph;
         tcph = (tcp_header *) (packet + eth_header_len + (IP_HL(ip4)*4));
         // printf("[*] IPv4 PROTOCOL TYPE TCP:\n");
         cx_track(ip_src, tcph->src_port, ip_dst, tcph->dst_port, ip4->ip_p, p_bytes, tcph->t_flags, tstamp, AF_INET);
         inpacket = 0;
         return;
      }
      else if (ip4->ip_p == IP_PROTO_UDP) {
         udp_header *udph;
         udph = (udp_header *) (packet + eth_header_len + (IP_HL(ip4)*4));
         // printf("[*] IPv4 PROTOCOL TYPE UDP:\n");
         cx_track(ip_src, udph->src_port, ip_dst, udph->dst_port, ip4->ip_p, p_bytes, 0, tstamp, AF_INET);
         inpacket = 0;
         return;
      }
      else if (ip4->ip_p == IP_PROTO_ICMP) {
         icmp_header *icmph;
         icmph = (icmp_header *) (packet + eth_header_len + (IP_HL(ip4)*4));
         // printf("[*] IP PROTOCOL TYPE ICMP\n");
         cx_track(ip_src, icmph->s_icmp_id, ip_dst, icmph->s_icmp_id, ip4->ip_p, p_bytes, 0, tstamp, AF_INET);
         inpacket = 0;
         return;
      }
      else {
         // printf("[*] IPv4 PROTOCOL TYPE OTHER: %d\n",ip4->ip_p);
         cx_track(ip_src, ip4->ip_p, ip_dst, ip4->ip_p, ip4->ip_p, p_bytes, 0, tstamp, AF_INET);
         inpacket = 0;
         return;
      }
   }

   else if ( eth_type == ETHERNET_TYPE_IPV6) {
      // printf("[*] Got IPv6 Packet...\n");
      ip6_header *ip6;
      ip6 = (ip6_header *) (packet + eth_header_len);
      if ( ip6->next == IP_PROTO_TCP ) {
         tcp_header *tcph;
         tcph = (tcp_header *) (packet + eth_header_len + IP6_HEADER_LEN);
         // printf("[*] IPv6 PROTOCOL TYPE TCP:\n");
         cx_track(ip6->ip_src, tcph->src_port, ip6->ip_dst, tcph->dst_port, ip6->next, ip6->len, tcph->t_flags, tstamp, AF_INET6);
         inpacket = 0;
         return;
      }
      else if (ip6->next == IP_PROTO_UDP) {
         udp_header *udph;
         udph = (udp_header *) (packet + eth_header_len + IP6_HEADER_LEN);
         // printf("[*] IPv6 PROTOCOL TYPE UDP:\n");
         cx_track(ip6->ip_src, udph->src_port, ip6->ip_dst, udph->dst_port, ip6->next, ip6->len, 0, tstamp, AF_INET6);
         inpacket = 0;
         return;
      }
      else if (ip6->next == IP6_PROTO_ICMP) {
         icmp6_header *icmph;
         icmph = (icmp6_header *) (packet + eth_header_len + IP6_HEADER_LEN);
         // printf("[*] IPv6 PROTOCOL TYPE ICMP\n");
         cx_track(ip6->ip_src, ip6->hop_lmt, ip6->ip_dst, ip6->hop_lmt, ip6->next, ip6->len, 0, tstamp, AF_INET6);
         inpacket = 0;
         return;
      }
      else {
         // printf("[*] IPv6 PROTOCOL TYPE OTHER: %d\n",ip6->next);
         cx_track(ip6->ip_src, ip6->next, ip6->ip_dst, ip6->next, ip6->next, ip6->len, 0, tstamp, AF_INET6);
         inpacket = 0;
         return;
      }
   }
   */
   inpacket = 0;
   return;
}
static void usage() {
    printf("edd: Entropy DDoS Detection\n\n");
    printf("USAGE:\n");
    printf(" $ %s [options]\n", BIN_NAME);
    printf("\n");
    printf(" OPTIONS:\n");
    printf("\n");
    printf(" -i             : network device (default: eth0)\n");
    printf(" -b             : berkeley packet filter\n");
    printf(" -d             : directory to dump sessions files in\n");
    printf(" -u             : user\n");
    printf(" -g             : group\n");
    printf(" -D             : enables daemon mode\n");
    printf(" -T             : dir to chroot into\n");
    printf(" -h             : this help message\n");
    printf(" -v             : verbose\n\n");
}

static int set_chroot(void) {
   char *absdir;
   char *logdir;
   int abslen;
   
   /* logdir = get_abs_path(logpath); */

   /* change to the directory */
   if ( chdir(chroot_dir) != 0 ) {
      printf("set_chroot: Can not chdir to \"%s\": %s\n",chroot_dir,strerror(errno));
   }

   /* always returns an absolute pathname */
   absdir = getcwd(NULL, 0);
   abslen = strlen(absdir);
   
   /* make the chroot call */
   if ( chroot(absdir) < 0 ) {
      printf("Can not chroot to \"%s\": absolute: %s: %s\n",chroot_dir,absdir,strerror(errno));
   }

   if ( chdir("/") < 0 ) {
        printf("Can not chdir to \"/\" after chroot: %s\n",strerror(errno));
   }   

   return 0;
}

static int drop_privs(void) {
   struct group *gr;
   struct passwd *pw;
   char *endptr;
   int i;
   int do_setuid = 0;
   int do_setgid = 0;
   unsigned long groupid = 0;
   unsigned long userid = 0;

   if ( group_name != NULL ) {
      do_setgid = 1;
      if( isdigit(group_name[0]) == 0 ) {
         gr = getgrnam(group_name);
         groupid = gr->gr_gid;
      }
      else {
         groupid = strtoul(group_name, &endptr, 10);
      }        
   }
    
   if ( user_name != NULL ) {
      do_setuid = 1;
      do_setgid = 1;
      if ( isdigit(user_name[0]) == 0 ) {
         pw = getpwnam(user_name);
         userid = pw->pw_uid;
      } else {
         userid = strtoul(user_name, &endptr, 10);
         pw = getpwuid(userid);
      }
        
      if ( group_name == NULL ) {
         groupid = pw->pw_gid;
      }
   }

   if ( do_setgid ) {
      if ( (i = setgid(groupid)) < 0 ) {
         printf("Unable to set group ID: %s", strerror(i));
      }
   }
    
   endgrent();
   endpwent();
    
   if ( do_setuid ) {
      if (getuid() == 0 && initgroups(user_name, groupid) < 0 ) {
         printf("Unable to init group names (%s/%lu)", user_name, groupid);
      }
      if ( (i = setuid(userid)) < 0 ) {
         printf("Unable to set user ID: %s\n", strerror(i));
      }
   }
   return 0;
}

static int is_valid_path(char *path) {
   struct stat st;

   if ( path == NULL ) {
      return 0;
   }
   if ( stat(path, &st) != 0 ) {
      return 0;
   }
   if ( !S_ISDIR(st.st_mode) || access(path, W_OK) == -1 ) {
      return 0;
   }
   return 1;
}

static int create_pid_file(char *path, char *filename) {
   char filepath[STDBUF];
   char *fp = NULL;
   char *fn = NULL;
   char pid_buffer[12];
   struct flock lock;
   int rval;
   int fd;

   memset(filepath, 0, STDBUF);

   if ( !filename ) {
      fn = pidfile;
   }
   else {
      fn = filename;
   }

   if ( !path ) {
      fp = pidpath;
   }
   else {
      fp = path;
   }

   if ( is_valid_path(fp) ) {
      snprintf(filepath, STDBUF-1, "%s/%s", fp, fn);
   }
   else {
      printf("PID path \"%s\" isn't a writeable directory!", fp);
   }
   
   true_pid_name = strdup(filename);
   
   if ( (fd = open(filepath, O_CREAT | O_WRONLY,
                    S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH)) == -1 ) {
      return ERROR;
   }

   /* pid file locking */
   lock.l_type = F_WRLCK;
   lock.l_start = 0;
   lock.l_whence = SEEK_SET;
   lock.l_len = 0;

   if ( fcntl(fd, F_SETLK, &lock) == -1 ) {
      if ( errno == EACCES || errno == EAGAIN ) {
         rval = ERROR;
      }
      else {
         rval = ERROR;
      }
      close(fd);
      return rval;
   }

   snprintf(pid_buffer, sizeof(pid_buffer), "%d\n", (int) getpid());
   if ( ftruncate(fd, 0) != 0 ) { return ERROR; }
   if ( write(fd, pid_buffer, strlen(pid_buffer)) != 0 ) { return ERROR; }
   return SUCCESS;
}
int daemonize() {
   pid_t pid;
   int fd;

   pid = fork();

   if ( pid > 0 ) {
      exit(0); /* parent */
   }

   use_syslog = 1;
   if ( pid < 0 ) {
      return ERROR;
   }

   /* new process group */
   setsid();

   /* close file handles */
   if ( (fd = open("/dev/null", O_RDWR)) >= 0 ) {
      dup2(fd, 0);
      dup2(fd, 1);
      dup2(fd, 2);
      if ( fd > 2 ) {
         close(fd);
      }
   }

   if ( pidfile ) {
      return create_pid_file(pidpath, pidfile);
   }

   return SUCCESS;
}

int main(int argc, char *argv[]) {

   int ch, fromfile, setfilter, version, drop_privs_flag, daemon_flag, chroot_flag;
   int use_syslog = 0;
   struct in_addr addr;
   struct bpf_program cfilter;
   char *bpff, errbuf[PCAP_ERRBUF_SIZE], *user_filter;
   char *net_ip_string;
   bpf_u_int32 net_mask;
   ch = fromfile = setfilter = version = drop_privs_flag = daemon_flag = 0;
   dev = "eth0";
   bpff = "";
   chroot_dir = "/tmp/";
   dpath = "./";
   inpacket = intr_flag = chroot_flag = 0;
   timecnt = time(NULL);
   
   /* test it! */
   uint8_t  b[18];
   memset((void*) b, 1, 17);
   b[17]= 0x11;  // the faulty bits

   printf("KnR %lu\n", count_bits(b,17));
   printf("KaW %lu\n", count_bits_kw(b,17));
   printf("PaP %lu\n", count_bits_pp(b,17));
   printf("JaP %lu\n", count_bits_p(b,17));
   printf("P64 %lu\n", count_bits_64(b,17));
   printf("T 1 %lu\n", count_bits_t1(b,17));
   printf("T 2 %lu\n", count_bits_t2(b,17));

   printf("weirdness test: %lu %lu %lu %lu %lu %lu\n", 
          count_bits_pp(b,17),
          count_bits_pp(b,17),
          count_bits_pp(b,17),
          count_bits_pp(b,17),
          count_bits_pp(b,17),
          count_bits_pp(b,17));

   signal(SIGTERM, game_over);
   signal(SIGINT,  game_over);
   signal(SIGQUIT, game_over);
   //signal(SIGHUP,  dump_active);
   //signal(SIGALRM, set_end_sessions); 

   while ((ch = getopt(argc, argv, "b:d:DT:g:hi:p:P:u:v")) != -1)
   switch (ch) {
      case 'i':
         dev = strdup(optarg);
         break;
      case 'b':
         bpff = strdup(optarg);
         break;
      case 'v':
         verbose = 1;
         break;
      case 'd':
         dpath = strdup(optarg);
         break;
      case 'h':
         usage();
         exit(0);
         break;
      case 'D':
         daemon_flag = 1;
         break;
      case 'T':
         chroot_flag = 1;
         break;
      case 'u':
         user_name = strdup(optarg);
         drop_privs_flag = 1;
         break;
      case 'g':
         group_name = strdup(optarg);
         drop_privs_flag = 1;
         break;
      case 'p':
         pidfile = strdup(optarg);
         break;
      case 'P':
         pidpath = strdup(optarg);
         break;
      default:
         exit(1);
         break;
   }

   printf("[*] Running  %s v %s\n", BIN_NAME, VERSION);


   if (getuid()) {
      printf("[*] You must be root..\n");
      return (1);
   }

   errbuf[0] = '\0';
   /* look up an availible device if non specified */
   if (dev == 0x0) dev = pcap_lookupdev(errbuf);
   printf("[*] Device: %s\n", dev);

   if ((handle = pcap_open_live(dev, SNAPLENGTH, 1, 500, errbuf)) == NULL) {
      printf("[*] Error pcap_open_live: %s \n", errbuf);
      pcap_close(handle);
      exit(1);
   }
   else if ((pcap_compile(handle, &cfilter, bpff, 1 ,net_mask)) == -1) {
      printf("[*] Error pcap_compile user_filter: %s\n", pcap_geterr(handle));
      pcap_close(handle);
      exit(1);
   }

   pcap_setfilter(handle, &cfilter);
   pcap_freecode(&cfilter); // filter code not needed after setfilter

   /* B0rk if we see an error... */
   if (strlen(errbuf) > 0) {
      printf("[*] Error errbuf: %s \n", errbuf);
      pcap_close(handle);
      exit(1);
   }

   if ( chroot_flag == 1 ) {
      set_chroot();
   }

   if(daemon_flag) {
      if(!is_valid_path(pidpath)){
         printf("[*] PID path \"%s\" is bad, check privilege.",pidpath);
         exit(1);
      }
      openlog("ppacket", LOG_PID | LOG_CONS, LOG_DAEMON);
      printf("[*] Daemonizing...\n\n");
      daemonize(NULL);
   }

   if(drop_privs_flag) {
      printf("[*] Dropping privs...\n\n");
      drop_privs();
   } 

   //alarm(TIMEOUT);
   printf("[*] Sniffing... need %lu packets for operation\n\n", P_WINDOW);
   pcap_loop(handle,-1,got_packet,NULL);

   pcap_close(handle);
   return(0);
}
