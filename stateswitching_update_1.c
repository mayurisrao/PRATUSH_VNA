/*
pratush_acq_v1_sanjay_pi 
data acquisition and state switching segment (Dec 6, 2021)
*/

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <ncurses.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/ioctl.h>
#include <bits/socket.h>
#include <sys/select.h>
#include <netinet/in.h>
#include <netinet/ether.h>
#include <netinet/tcp.h>
#include <netinet/udp.h>
#include <netinet/ip.h>
#include <netinet/if_ether.h>
#include <net/ethernet.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <signal.h>

#include <math.h>
#include <complex.h>

#include <time.h>
#include <sys/timeb.h>
#include <sys/time.h>
#include <casacore/mirlib/maxdimc.h>
#include <casacore/mirlib/miriad.h>

#include <termios.h>
#include <fcntl.h>
#include <sys/signal.h>
#include <wiringPi.h>

typedef char	        S8;  					/* Signed 8-bit integer (character) */
typedef unsigned char   U8;  					/* Unsigned 8-bit integer (byte)    */
typedef signed short    S16; 					/* Signed 16-bit integer (word)     */
typedef unsigned short  U16; 					/* Unsigned 16-bit integer (word)   */
typedef signed long     S32; 					/* Signed 32-bit integer (long)     */
typedef unsigned long   U32; 					/* Unsigned 32-bit integer (long)   */
typedef float           FLT; 					/* 4-byte single precision (float)  */
typedef double          DBL; 					/* 8-byte double precision (double) */
const int pins[8] = {29, 31, 32, 36, 37, 38, 40};

#define SIZE 256
#define PI 3.14159265358979

#define MAXLEN 100
#define CONFIG_FILE "SARAS_Config.txt"

#define SOCKETS_IP_ADDRESS	"192.168.1.93"
#define SOCKETS_PORT		53503
#define SOCKETS_TIMEOUT		10

#define BAUDRATE B9600
#define device "/dev/mydev"

#define _POSIX_SOURCE 1
#define FALSE 0
#define TRUE 1
#define ESCAPE CTRL('[')
#define LOCAL_TIME_HR 5
#define LOCAL_TIME_MM 30

#define MSG_IN_ERROR     -1
#define MSG_IN_COMPLETE  0

#define TSIP_DLE         1
#define TSIP_IN_PARTIAL  2

#define MSG_IN_COMPLETE  0
#define TSIP_DLE         1
#define TSIP_IN_PARTIAL  2

#define DLE              0x10 					// TSIP packet start/end header         
#define ETX              0x03 					// TSIP data packet tail                
#define MAX_TSIP_PKT_LEN 300  					// max length of a TSIP packet 

void setup_gps();
//void setup_rpi();
//void state_sw_rpi(char input_data[6]);
//void state_sw_rpi_1(char input_data[6]);
void Parse0x8F (unsigned char ucData[], int nLen);

// System time related variables
const struct tm *tm ;
const struct stat st;
struct timeb cur_time_struct2;
struct tm *ut_time;
struct tm *cur_time_struct;
long cur_time_long;
unsigned short millitime;
float timesec[16];
time_t timep;
int time_usec;
clock_t startt,endt;

// UTC time variables    
int utc_hh,utc_mm,utc_ss,utc_day,utc_month,utc_year,utc_flag;

// Input-related variables
long int size,temp;
//const int M=8;                        				// Number of parallel, pipelined N-point FFTs 
//const int N=2048;                     				// Length of each pipelined FFT
size_t count=0;
int tno,l,data_ind=1, flag=0, dpkt, start=0, stop=0,len,next;
long int zero_len=10, start_ind=0, stop_ind=0;

// Memory allocation variables
unsigned char *stage = NULL;
unsigned char *chan_data = NULL;
FILE *logfile, *dat_out;
unsigned int result;
int datasock; // Socket ids for various UDP logical links (sockets)
int startstop_pi = 6;

/* --- Function kbhit(), a keyboard lookahead monitor --- */
int kbhit(void)
{
  	int cnt = 0;
  	int error;
  	static struct termios Otty, Ntty;

  	tcgetattr(0, &Otty);
  	Ntty = Otty;

  	Ntty.c_iflag          = 0;       /* input mode                */
	Ntty.c_oflag          = 0;       /* output mode               */
  	Ntty.c_lflag         &= ~ICANON; /* raw mode */
  	Ntty.c_cc[VMIN]       = CMIN;    /* minimum characters to wait for  */
  	Ntty.c_cc[VTIME]      = CTIME;   /* minimum time to wait */

  	if (0 == (error = tcsetattr(0, TCSANOW, &Ntty))) 
	{
    		struct timeval      tv;
    		error     += ioctl(0, FIONREAD, &cnt);
    		error     += tcsetattr(0, TCSANOW, &Otty);
    		tv.tv_sec  = 0;
    		tv.tv_usec = 100;
    		select(1, NULL, NULL, NULL, &tv);
  	}

  	return (error == 0 ? cnt : -1 );
}

double cal_lst(double utc_julian_date, double longitude_radians)
{
	int julian_day,day_of_year;
	long int yyyy,mmmm,dddd,jjdd;
	double ut1_julian_date,time_ut1,gmst,lst,gast,dut1,utd,by,mjd;
	double dd,TT,HH,JD0,D0,DD;
	double ee, LL, OO, DP, eqeq;
	const double pi=3.14159265358979;

	mjd = utc_julian_date - 2400000.5;   /* Modified Julian Date */
	by = 1900.0 + (utc_julian_date - 2415020.31352) / 365.242198;   /* Besselian year */	
 
	utd = (0.022*sin(2*pi*by)) - (0.012*cos(2*pi*by)) - (0.006*sin(4*pi*by)) + (0.007*cos(4*pi*by)); 
	/* UTD = UT2-UT1 */ 	
	dut1 = 0.3523 - (0.00113*(mjd - 57955)) - utd;  /* DUT1 = UT1-UTC */

	ut1_julian_date = utc_julian_date + (double)dut1/(3600.0*24.0); 

	julian_day = (int)floor(ut1_julian_date + 0.5);
	time_ut1 = (ut1_julian_date+0.5) - (double)julian_day;
	if(time_ut1 >= 1.0) time_ut1 -= 1.0;
	if(time_ut1 < 0.0) time_ut1 += 1.0;
	JD0 = (double)julian_day - 0.5;
	HH = (ut1_julian_date - (double)JD0)*24.0;
	D0 = JD0 - 2451545.0;
	DD = ut1_julian_date - 2451545.0;
	TT = DD/36525.0;

	gmst = 6.697374558 + 0.06570982441908 * D0 + 1.00273790935 * HH + 0.000026 * TT*TT;
	while(gmst>=24.0) gmst -= 24.0;
	while(gmst<0.0) gmst += 24.0;

	ee = 23.4393 - 0.0000004 * DD;
	LL = 280.47 + 0.98565 * DD;
	OO = 125.04 - 0.052954 * DD;
	
	ee *= pi/180.0;
	LL *= pi/180.0;
	OO *= pi/180.0;

	DP = -0.000319*sin(OO) - 0.000024*sin(2*LL);
	eqeq = DP * cos(ee);

	gast = gmst + eqeq;

	lst = gast + (longitude_radians*180.0/pi)*(24.0/360.0);
	if(lst>24.0) lst -= 24.0;
	if(lst<0.0) lst += 24.0;

	lst *= (360.0*pi)/(24.0*180.0);
	
	return lst;
}

struct sample_parameters
{
  char var1[MAXLEN];

  char var2[MAXLEN];

  char var3[MAXLEN];

  char var4[MAXLEN];

  char var5[MAXLEN];
  
  char var6[MAXLEN];

  char var7[MAXLEN];

  char var8_1[MAXLEN];
  char var8_2[MAXLEN];
  char var8_3[MAXLEN];
  char var8_4[MAXLEN];
  char var8_5[MAXLEN];
  char var8_6[MAXLEN];
  char var8_7[MAXLEN];
  char var8_8[MAXLEN];
  
  char var9_1[MAXLEN];
  char var9_2[MAXLEN];
  char var9_3[MAXLEN];
  char var9_4[MAXLEN];
  char var9_5[MAXLEN];
  char var9_6[MAXLEN];
  char var9_7[MAXLEN];
  char var9_8[MAXLEN];
  
  char var10_1[MAXLEN];
  char var10_2[MAXLEN];
  char var10_3[MAXLEN];
  char var10_4[MAXLEN];
  char var10_5[MAXLEN];
  char var10_6[MAXLEN];
  char var10_7[MAXLEN];
  char var10_8[MAXLEN];
  
  char var11_1[MAXLEN];
  char var11_2[MAXLEN];
  char var11_3[MAXLEN];
  char var11_4[MAXLEN];
  char var11_5[MAXLEN];
  char var11_6[MAXLEN];
  char var11_7[MAXLEN];
  char var11_8[MAXLEN];
  
  char var12_1[MAXLEN];
  char var12_2[MAXLEN];
  char var12_3[MAXLEN];
  char var12_4[MAXLEN];
  char var12_5[MAXLEN];
  char var12_6[MAXLEN];
  char var12_7[MAXLEN];
  char var12_8[MAXLEN];
  
  char var13_1[MAXLEN];
  char var13_2[MAXLEN];
  char var13_3[MAXLEN];
  char var13_4[MAXLEN];
  char var13_5[MAXLEN];
  char var13_6[MAXLEN];
  char var13_7[MAXLEN];
  char var13_8[MAXLEN];
  
  char var14_1[MAXLEN];
  char var14_2[MAXLEN];
  char var14_3[MAXLEN];
  char var14_4[MAXLEN];
  char var14_5[MAXLEN];
  char var14_6[MAXLEN];
  char var14_7[MAXLEN];
  char var14_8[MAXLEN];
  
  char var15_1[MAXLEN];
  char var15_2[MAXLEN];
  char var15_3[MAXLEN];
  char var15_4[MAXLEN];
  char var15_5[MAXLEN];
  char var15_6[MAXLEN];
  char var15_7[MAXLEN];
  char var15_8[MAXLEN];

  char var16[MAXLEN];

  char var17[MAXLEN];

  char var18[MAXLEN];
}
  sample_parameters;

/*
 * initialize data to default values
 */
void
init_parameters (struct sample_parameters * parms)
{

}

char *
trim (char * s)
{
  char *s1 = s, *s2 = &s[strlen (s) - 1];

  while ( (isspace (*s2)) && (s2 >= s1) )
    s2--;
  *(s2+1) = '\0';

  while ( (isspace (*s1)) && (s1 < s2) )
    s1++;

  strcpy (s, s1);
  return s;
}

void
parse_config (struct sample_parameters * parms)
{
  char *s, buff[256];
  FILE *fp = fopen (CONFIG_FILE, "r");
  if (fp == NULL)
  {
    return;
  }

  while ((s = fgets (buff, sizeof buff, fp)) != NULL)
  {
    if (buff[0] == '\n' || buff[0] == '#')
      continue;

    char name[MAXLEN], value[MAXLEN];
    s = strtok (buff, "=");
    if (s==NULL)
      continue;
    else
      strncpy (name, s, MAXLEN);
    s = strtok (NULL, "=");
    if (s==NULL)
      continue;
    else
      strncpy (value, s, MAXLEN);
    trim (value);

    if (strcmp(name, "Num_FirmwareBuffers")==0)
      strncpy (parms->var1, value, MAXLEN);

    else if (strcmp(name, "Firmware_BufferDepth")==0)
      strncpy (parms->var2, value, MAXLEN);

    else if (strcmp(name, "Firmware_buffer_locationDepth")==0)
      strncpy (parms->var3, value, MAXLEN);

    else if (strcmp(name, "NumFFTframes")==0)
      strncpy (parms->var4, value, MAXLEN);

    else if (strcmp(name, "pktsize")==0)
      strncpy (parms->var5, value, MAXLEN);

    else if (strcmp(name, "headersize")==0)
      strncpy (parms->var17, value, MAXLEN);

	else if (strcmp(name, "npkt")==0)
      strncpy (parms->var18, value, MAXLEN);

	else if (strcmp(name, "Num_chan_paths")==0)
      strncpy (parms->var16, value, MAXLEN);

    else if (strcmp(name, "SelfCorrPattern")==0)
      strncpy (parms->var6, value, MAXLEN);

    else if (strcmp(name, "CrossCorrPattern")==0)
      strncpy (parms->var7, value, MAXLEN);

    else if (strcmp(name, "chan1_path_00")==0)
      strncpy (parms->var8_1, value, MAXLEN);
    else if (strcmp(name, "chan1_path_01")==0)
      strncpy (parms->var8_2, value, MAXLEN);
    else if (strcmp(name, "chan1_path_02")==0)
      strncpy (parms->var8_3, value, MAXLEN);
    else if (strcmp(name, "chan1_path_03")==0)
      strncpy (parms->var8_4, value, MAXLEN);
    else if (strcmp(name, "chan1_path_04")==0)
      strncpy (parms->var8_5, value, MAXLEN);
    else if (strcmp(name, "chan1_path_05")==0)
      strncpy (parms->var8_6, value, MAXLEN);
    else if (strcmp(name, "chan1_path_06")==0)
      strncpy (parms->var8_7, value, MAXLEN);
    else if (strcmp(name, "chan1_path_07")==0)
      strncpy (parms->var8_8, value, MAXLEN);
      
    else if (strcmp(name, "chan2_path_00")==0)
      strncpy (parms->var9_1, value, MAXLEN);
    else if (strcmp(name, "chan2_path_01")==0)
      strncpy (parms->var9_2, value, MAXLEN);
    else if (strcmp(name, "chan2_path_02")==0)
      strncpy (parms->var9_3, value, MAXLEN);
    else if (strcmp(name, "chan2_path_03")==0)
      strncpy (parms->var9_4, value, MAXLEN);
    else if (strcmp(name, "chan2_path_04")==0)
      strncpy (parms->var9_5, value, MAXLEN);
    else if (strcmp(name, "chan2_path_05")==0)
      strncpy (parms->var9_6, value, MAXLEN);
    else if (strcmp(name, "chan2_path_06")==0)
      strncpy (parms->var9_7, value, MAXLEN);
    else if (strcmp(name, "chan2_path_07")==0)
      strncpy (parms->var9_8, value, MAXLEN);
      
    else if (strcmp(name, "cc_real_00")==0)
      strncpy (parms->var10_1, value, MAXLEN);
    else if (strcmp(name, "cc_real_01")==0)
      strncpy (parms->var10_2, value, MAXLEN);
    else if (strcmp(name, "cc_real_02")==0)
      strncpy (parms->var10_3, value, MAXLEN);
    else if (strcmp(name, "cc_real_03")==0)
      strncpy (parms->var10_4, value, MAXLEN);
    else if (strcmp(name, "cc_real_04")==0)
      strncpy (parms->var10_5, value, MAXLEN);
    else if (strcmp(name, "cc_real_05")==0)
      strncpy (parms->var10_6, value, MAXLEN);
    else if (strcmp(name, "cc_real_06")==0)
      strncpy (parms->var10_7, value, MAXLEN);
    else if (strcmp(name, "cc_real_07")==0)
      strncpy (parms->var10_8, value, MAXLEN);

    else if (strcmp(name, "cc_img_00")==0)
      strncpy (parms->var11_1, value, MAXLEN);
    else if (strcmp(name, "cc_img_01")==0)
      strncpy (parms->var11_2, value, MAXLEN);
    else if (strcmp(name, "cc_img_02")==0)
      strncpy (parms->var11_3, value, MAXLEN);
    else if (strcmp(name, "cc_img_03")==0)
      strncpy (parms->var11_4, value, MAXLEN);
    else if (strcmp(name, "cc_img_04")==0)
      strncpy (parms->var11_5, value, MAXLEN);
    else if (strcmp(name, "cc_img_05")==0)
      strncpy (parms->var11_6, value, MAXLEN);
    else if (strcmp(name, "cc_img_06")==0)
      strncpy (parms->var11_7, value, MAXLEN);
    else if (strcmp(name, "cc_img_07")==0)
      strncpy (parms->var11_8, value, MAXLEN);
      
    else if (strcmp(name, "chan1_ind_00")==0)
      strncpy (parms->var12_1, value, MAXLEN);
    else if (strcmp(name, "chan1_ind_01")==0)
      strncpy (parms->var12_2, value, MAXLEN);
    else if (strcmp(name, "chan1_ind_02")==0)
      strncpy (parms->var12_3, value, MAXLEN);
    else if (strcmp(name, "chan1_ind_03")==0)
      strncpy (parms->var12_4, value, MAXLEN);
    else if (strcmp(name, "chan1_ind_04")==0)
      strncpy (parms->var12_5, value, MAXLEN);
    else if (strcmp(name, "chan1_ind_05")==0)
      strncpy (parms->var12_6, value, MAXLEN);
    else if (strcmp(name, "chan1_ind_06")==0)
      strncpy (parms->var12_7, value, MAXLEN);
    else if (strcmp(name, "chan1_ind_07")==0)
      strncpy (parms->var12_8, value, MAXLEN);
      
    else if (strcmp(name, "chan2_ind_00")==0)
      strncpy (parms->var13_1, value, MAXLEN);
    else if (strcmp(name, "chan2_ind_01")==0)
      strncpy (parms->var13_2, value, MAXLEN);
    else if (strcmp(name, "chan2_ind_02")==0)
      strncpy (parms->var13_3, value, MAXLEN);
    else if (strcmp(name, "chan2_ind_03")==0)
      strncpy (parms->var13_4, value, MAXLEN);
    else if (strcmp(name, "chan2_ind_04")==0)
      strncpy (parms->var13_5, value, MAXLEN);
    else if (strcmp(name, "chan2_ind_05")==0)
      strncpy (parms->var13_6, value, MAXLEN);
    else if (strcmp(name, "chan2_ind_06")==0)
      strncpy (parms->var13_7, value, MAXLEN);
    else if (strcmp(name, "chan2_ind_07")==0)
      strncpy (parms->var13_8, value, MAXLEN);
      
    else if (strcmp(name, "cc_real_ind_00")==0)
      strncpy (parms->var14_1, value, MAXLEN);
    else if (strcmp(name, "cc_real_ind_01")==0)
      strncpy (parms->var14_2, value, MAXLEN);
    else if (strcmp(name, "cc_real_ind_02")==0)
      strncpy (parms->var14_3, value, MAXLEN);
    else if (strcmp(name, "cc_real_ind_03")==0)
      strncpy (parms->var14_4, value, MAXLEN);
    else if (strcmp(name, "cc_real_ind_04")==0)
      strncpy (parms->var14_5, value, MAXLEN);
    else if (strcmp(name, "cc_real_ind_05")==0)
      strncpy (parms->var14_6, value, MAXLEN);
    else if (strcmp(name, "cc_real_ind_06")==0)
      strncpy (parms->var14_7, value, MAXLEN);
    else if (strcmp(name, "cc_real_ind_07")==0)
      strncpy (parms->var14_8, value, MAXLEN);
      
    else if (strcmp(name, "cc_img_ind_00")==0)
      strncpy (parms->var15_1, value, MAXLEN);
    else if (strcmp(name, "cc_img_ind_01")==0)
      strncpy (parms->var15_2, value, MAXLEN);
    else if (strcmp(name, "cc_img_ind_02")==0)
      strncpy (parms->var15_3, value, MAXLEN);
    else if (strcmp(name, "cc_img_ind_03")==0)
      strncpy (parms->var15_4, value, MAXLEN);
    else if (strcmp(name, "cc_img_ind_04")==0)
      strncpy (parms->var15_5, value, MAXLEN);
    else if (strcmp(name, "cc_img_ind_05")==0)
      strncpy (parms->var15_6, value, MAXLEN);
    else if (strcmp(name, "cc_img_ind_06")==0)
      strncpy (parms->var15_7, value, MAXLEN);
    else if (strcmp(name, "cc_img_ind_07")==0)
      strncpy (parms->var15_8, value, MAXLEN);
      
   
  }

  fclose (fp);
}
//const int pins[8] = {29, 31, 32, 36, 37, 38, 40};
int fe_on_off_1=3; // Front end power on/off 25012019
int led_1 = 8;
int ledpin_1 = 10;
int startstop_pi_1 = 6;
float tempc_1 = 0; // temperature variables
int fe_flag_1 = 0; //Front-end comes on only if this is set to '1' 30 Jan 2019
int r;
 void setup_rpi() {
    // Set up each pin as an output
    pinMode(pins[1], OUTPUT);
    pinMode(pins[2], OUTPUT);
    pinMode(pins[3], OUTPUT);
    pinMode(pins[4], OUTPUT);
    pinMode(pins[5], OUTPUT);
    pinMode(pins[6], OUTPUT);
    pinMode(pins[7], OUTPUT);
}

void pin_intermidiatestate(const int pins[8])
{ 
      digitalWrite(pins[1],LOW);    
      digitalWrite(pins[2],LOW);   
      digitalWrite(pins[3],LOW); 
      digitalWrite(pins[4],LOW); 
      digitalWrite(pins[5],LOW); 
      digitalWrite(pins[6],LOW);
      digitalWrite(pins[7],LOW);  
      delay(9000);
}

void pin_laststate(const int pins[8])
{
      digitalWrite(pins[1],HIGH);    
      digitalWrite(pins[2],HIGH);   
      digitalWrite(pins[3],HIGH); 
      digitalWrite(pins[4],HIGH); 
      digitalWrite(pins[5],LOW); 
      digitalWrite(pins[6],LOW);
      digitalWrite(pins[7],LOW);  
      delay(1000);
}


int inint;
void state_sw_rpi_vna(const int pins[8],int num_of_ints,char source_name[9],float temperature)
{
    delay(1000);//delay of 1 sec added back by Naren 25 july 
    tempc_1=0;  //tempc = tempc/8.0; // better precision
 
  if( tempc_1 < 40.0)  
  {
    digitalWrite(ledpin_1,HIGH);
    digitalWrite(led_1, LOW);
  }
  else
  {
    digitalWrite(ledpin_1,LOW);
    digitalWrite(led_1, HIGH);
  }
  setup_rpi();
  pinMode(startstop_pi, OUTPUT);
  //int inint=num_of_int;
  //char source_name;/usr/include/stdio.h:354:39: note: expected ‘char * restrict’ but argument is of type ‘char **’

  // Set source name for this integration
  
  if (inint%4 == 0) {
  snprintf(source_name,8,"OPEN");
  }
  else if(inint%4 == 1) {
  snprintf(source_name,8,"SHORT");
  }
  else if(inint%4 == 2) {
  snprintf(source_name,8,"LOAD");
  }
  else if(inint%4 == 3) {
  snprintf(source_name,8,"ANTENNA");
  }
               
          
				/*if(inint%4==0)
				{
					/*source_name[0]='O';
					source_name[1]='P';
					source_name[2]='E';
					source_name[3]='N';
					source_name[4]=' ';
					source_name[5]=' ';
					source_name[6]=' ';
					source_name[7]='\0';
					sourcename[9]= 'OPEN\0'
					
				}
				else if(inint%4==1)
				{
					/*source_name[0]='S';
					source_name[1]='H';
					source_name[2]='O';
					source_name[3]='R';
					source_name[4]='T';
					source_name[5]=' ';
					source_name[6]=' ';
					source_name[7]='\0';
				        sourcename[9]= 'SHORT\0'
				}	
				else if(inint%4==2)
				{
				  source_name[0]='L';
					source_name[1]='O';
					source_name[2]='A';
					source_name[3]='D';
					source_name[4]=' ';
					source_name[5]=' ';
					source_name[6]=' ';
					source_name[7]='\0';
				}	
				else if(inint%4==3)
				{	
				        source_name[0]='A';
					source_name[1]='N';
					source_name[2]='T';
					source_name[3]='E';
					source_name[4]='N';
					source_name[5]='N';
					source_name[6]='A';
					source_name[7]='\0';
				}*/	
				
 
	  if (temperature < 40)
	  {
	  	if(inint%4==0)	// First integration of any cycle	
	    	{
			//temp1=0;
			//temp2=0;
			//temp3=0;
			digitalWrite(pins[1],HIGH);    
			digitalWrite(pins[2],LOW);   
			digitalWrite(pins[3],LOW); 
                       digitalWrite(pins[4],LOW); 
                       digitalWrite(pins[5],LOW); 
                       digitalWrite(pins[6],LOW);
                       digitalWrite(pins[7],LOW);  
	               delay(1000); 
	               pin_intermidiatestate( pins);
		}
	  	
	  	else
		 if(inint%4 == 1) 
	  	{
			//temp1=0;
			//temp2=0;
			//temp3=1;
		        digitalWrite(pins[1],LOW);    
			digitalWrite(pins[2],HIGH);   
			digitalWrite(pins[3],LOW); 
                       digitalWrite(pins[4],LOW); 
                       digitalWrite(pins[5],LOW); 
                       digitalWrite(pins[6],LOW);
                       digitalWrite(pins[7],LOW);  
			delay(1000);
			
	               pin_intermidiatestate( pins);
		}

	  	else
		 if(inint%4 == 2) 
	  	{
			//temp1=0;
			//temp2=1;
			//temp3=0;
			digitalWrite(pins[1],LOW);    
			digitalWrite(pins[2],LOW);   
			digitalWrite(pins[3],HIGH); 
                       digitalWrite(pins[4],LOW); 
                       digitalWrite(pins[5],LOW); 
                       digitalWrite(pins[6],LOW);
                       digitalWrite(pins[7],LOW);  
                       delay(1000);
			
	               pin_intermidiatestate( pins);
			    

      }	//setup_rpi();

	  	else
		 if(inint%4 == 3) 
	  	{
	                //temp1=0;
			//temp2=1;
			//temp3=1;
			digitalWrite(pins[1],LOW);    
			digitalWrite(pins[2],LOW);   
			digitalWrite(pins[3],LOW); 
                       digitalWrite(pins[4],HIGH); 
                       digitalWrite(pins[5],LOW); 
                       digitalWrite(pins[6],LOW);
                       digitalWrite(pins[7],LOW);  
			delay(1000); 
	                pin_intermidiatestate( pins);
                        pin_laststate(pins);
      }		    
}
}


int main(int argc, char *argv[])
{ 
  char *num_of_int_dummy = argv[1];
  char *total_num_of_int_dummy = argv[2];
  int num_of_int = atoi(num_of_int_dummy);
  int total_num_of_int = atoi(total_num_of_int_dummy);
  int nint = total_num_of_int;
  int inint;
  //long int *tp1
  //const int pins[8] = {29, 31, 32, 36, 37, 38, 40};

	
	struct sample_parameters parms;

    init_parameters (&parms);
    parse_config (&parms);
    
    int Num_FirmwareBuffers = atoi(parms.var1);
    
    int Firmware_BufferDepth =atoi(parms.var2);
    
    int Firmware_buffer_locationDepth =atoi(parms.var3);
    
    int NumFFTframes =atoi(parms.var4);
    
    int pktsize =atoi(parms.var5);

	int headersize =atoi(parms.var17);

	int npkt =atoi(parms.var18);
    
	int Num_chan_paths =atoi(parms.var16); 

    int SelfCorrPattern =atoi(parms.var6);
    int CrossCorrPattern =atoi(parms.var7);
    
    int chan1_path_00 =atoi(parms.var8_1);
    int chan1_path_01 =atoi(parms.var8_2);
    int chan1_path_02 =atoi(parms.var8_3);
    int chan1_path_03 =atoi(parms.var8_4);
    int chan1_path_04 =atoi(parms.var8_5);
    int chan1_path_05 =atoi(parms.var8_6);
    int chan1_path_06 =atoi(parms.var8_7);
    int chan1_path_07 =atoi(parms.var8_8);
    
    int chan2_path_00 =atoi(parms.var9_1);
    int chan2_path_01 =atoi(parms.var9_2);
    int chan2_path_02 =atoi(parms.var9_3);
    int chan2_path_03 =atoi(parms.var9_4);
    int chan2_path_04 =atoi(parms.var9_5);
    int chan2_path_05 =atoi(parms.var9_6);
    int chan2_path_06 =atoi(parms.var9_7);
    int chan2_path_07 =atoi(parms.var9_8);
    
    int cc_real_00 =atoi(parms.var10_1);
    int cc_real_01 =atoi(parms.var10_2);
    int cc_real_02 =atoi(parms.var10_3);
    int cc_real_03 =atoi(parms.var10_4);
    int cc_real_04 =atoi(parms.var10_5);
    int cc_real_05 =atoi(parms.var10_6);
    int cc_real_06 =atoi(parms.var10_7);
    int cc_real_07 =atoi(parms.var10_8);
    
    int cc_img_00 =atoi(parms.var11_1);
    int cc_img_01 =atoi(parms.var11_2);
    int cc_img_02 =atoi(parms.var11_3);
    int cc_img_03 =atoi(parms.var11_4);
    int cc_img_04 =atoi(parms.var11_5);
    int cc_img_05 =atoi(parms.var11_6);
    int cc_img_06 =atoi(parms.var11_7);
    int cc_img_07 =atoi(parms.var11_8);
    
    int chan1_ind_00 =atoi(parms.var12_1);
    int chan1_ind_01 =atoi(parms.var12_2);
    int chan1_ind_02 =atoi(parms.var12_3);
    int chan1_ind_03 =atoi(parms.var12_4);
    int chan1_ind_04 =atoi(parms.var12_5);
    int chan1_ind_05 =atoi(parms.var12_6);
    int chan1_ind_06 =atoi(parms.var12_7);
    int chan1_ind_07 =atoi(parms.var12_8);
    
    int chan2_ind_00 =atoi(parms.var13_1);
    int chan2_ind_01 =atoi(parms.var13_2);
    int chan2_ind_02 =atoi(parms.var13_3);
    int chan2_ind_03 =atoi(parms.var13_4);
    int chan2_ind_04 =atoi(parms.var13_5);
    int chan2_ind_05 =atoi(parms.var13_6);
    int chan2_ind_06 =atoi(parms.var13_7);
    int chan2_ind_07 =atoi(parms.var13_8);
    
    int cc_real_ind_00 =atoi(parms.var14_1);
    int cc_real_ind_01 =atoi(parms.var14_2);
    int cc_real_ind_02 =atoi(parms.var14_3);
    int cc_real_ind_03 =atoi(parms.var14_4);
    int cc_real_ind_04 =atoi(parms.var14_5);
    int cc_real_ind_05 =atoi(parms.var14_6);
    int cc_real_ind_06 =atoi(parms.var14_7);
    int cc_real_ind_07 =atoi(parms.var14_8);
    
    int cc_img_ind_00 =atoi(parms.var15_1);
    int cc_img_ind_01 =atoi(parms.var15_2);
    int cc_img_ind_02 =atoi(parms.var15_3);
    int cc_img_ind_03 =atoi(parms.var15_4);
    int cc_img_ind_04 =atoi(parms.var15_5);
    int cc_img_ind_05 =atoi(parms.var15_6);
    int cc_img_ind_06 =atoi(parms.var15_7);
    int cc_img_ind_07 =atoi(parms.var15_8);
    
    // Calculation of variable values from the configuration file data
    int initial_array_col_size = Firmware_BufferDepth * NumFFTframes; 
    int final_array_col_size = Num_FirmwareBuffers * Firmware_BufferDepth * NumFFTframes;
    int rcvbuf = Num_FirmwareBuffers * Firmware_BufferDepth * NumFFTframes * Num_chan_paths * Firmware_buffer_locationDepth * 2;
	dpkt = npkt/2;
	//printf("-----------------%d",initial_array_col_size);
  	long int i,k,j,ii,jj,zz,frame=0,n;
  	
	int chan1_path[8] = {chan1_path_00, chan1_path_01, chan1_path_02, chan1_path_03, chan1_path_04,chan1_path_05,chan1_path_06 ,chan1_path_07};
	int chan2_path[8] = {chan2_path_00, chan2_path_01, chan2_path_02, chan2_path_03, chan2_path_04,chan2_path_05,chan2_path_06 ,chan2_path_07};
	int cc_real[8] = {cc_real_00, cc_real_01, cc_real_02, cc_real_03, cc_real_04,cc_real_05,cc_real_06 ,cc_real_07};
	int cc_img[8] = {cc_img_00, cc_img_01, cc_img_02, cc_img_03, cc_img_04,cc_img_05,cc_img_06 ,cc_img_07};
	int chan1_ind[8] = {chan1_ind_00, chan1_ind_01, chan1_ind_02, chan1_ind_03, chan1_ind_04,chan1_ind_05,chan1_ind_06 ,chan1_ind_07};
	int chan2_ind[8] = {chan2_ind_00, chan2_ind_01, chan2_ind_02, chan2_ind_03, chan2_ind_04,chan2_ind_05,chan2_ind_06 ,chan2_ind_07};
	int cc_real_ind[8] = {cc_real_ind_00, cc_real_ind_01, cc_real_ind_02, cc_real_ind_03, cc_real_ind_04,cc_real_ind_05,cc_real_ind_06 ,cc_real_ind_07};
	int cc_img_ind[8] = {cc_img_ind_00, cc_img_ind_01, cc_img_ind_02, cc_img_ind_03, cc_img_ind_04,cc_img_ind_05,cc_img_ind_06 ,cc_img_ind_07};

    long int *tp1;
    //long int **img_reordered_crosscorr;

	long int **Start_AutoCorr_Chan1, **Start_AutoCorr_Chan2, **Start_CrossCorrRealPath, **Start_CrossCorrImgPath, **selfcorr_chan1_complex, **selfcorr_chan2_complex, **real_crosscorr_complex, **img_crosscorr_complex, **before_reorder_selfcorr1, **reordered_selfcorr1, **before_reorder_selfcorr2, **reordered_selfcorr2, **before_reorder_real_crosscorr, **real_reordered_crosscorr, **before_reorder_img_crosscorr, **img_reordered_crosscorr;

	long int *final_selfcorr1, *final_selfcorr2, *final_real_crosscorr, *final_img_crosscorr, *selfcorr1_avg, *selfcorr2_avg, *crosscorr_ravg, *crosscorr_iavg;

	int l1=0, i1=0;

    l1 = sizeof(int *) * Num_FirmwareBuffers + sizeof(int) * initial_array_col_size * Num_FirmwareBuffers;
    Start_AutoCorr_Chan1 		  = (long  int **)malloc(l1);
	Start_AutoCorr_Chan2 		  = (long  int **)malloc(l1);
	Start_CrossCorrRealPath 	  = (long  int **)malloc(l1);
	Start_CrossCorrImgPath 		  = (long  int **)malloc(l1);
	selfcorr_chan1_complex 		  = (long  int **)malloc(l1);
	selfcorr_chan2_complex 		  = (long  int **)malloc(l1);
	real_crosscorr_complex 		  = (long  int **)malloc(l1);
	img_crosscorr_complex 		  = (long  int **)malloc(l1);
	before_reorder_selfcorr1 	  = (long  int **)malloc(l1);
	reordered_selfcorr1			  = (long  int **)malloc(l1);
	before_reorder_selfcorr2 	  = (long  int **)malloc(l1);
	reordered_selfcorr2 		  = (long  int **)malloc(l1);
	before_reorder_real_crosscorr = (long  int **)malloc(l1);
	real_reordered_crosscorr      = (long  int **)malloc(l1);
	before_reorder_img_crosscorr  = (long  int **)malloc(l1);
	img_reordered_crosscorr       = (long  int **)malloc(l1);

	final_selfcorr1               = (long  int *)malloc(final_array_col_size * sizeof(int));
	final_selfcorr2        		  = (long  int *)malloc(final_array_col_size * sizeof(int));
	final_real_crosscorr          = (long  int *)malloc(final_array_col_size * sizeof(int));
	final_img_crosscorr           = (long  int *)malloc(final_array_col_size * sizeof(int));
	selfcorr1_avg                 = (long  int *)malloc(final_array_col_size * sizeof(int));
	selfcorr2_avg                 = (long  int *)malloc(final_array_col_size * sizeof(int));
	crosscorr_ravg 				  = (long  int *)malloc(final_array_col_size * sizeof(int));
	crosscorr_iavg                = (long  int *)malloc(final_array_col_size * sizeof(int));

    
    tp1 = (long  int *)(Start_AutoCorr_Chan1 + Num_FirmwareBuffers);
    for(int i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        Start_AutoCorr_Chan1[i1] = (tp1 + initial_array_col_size * i1);
	

	tp1 = (long  int *)(Start_AutoCorr_Chan2 + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        Start_AutoCorr_Chan2[i1] = (tp1 + initial_array_col_size * i1);


	tp1 = (long  int *)(Start_CrossCorrRealPath + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        Start_CrossCorrRealPath[i1] = (tp1 + initial_array_col_size * i1);


	tp1 = (long  int *)(Start_CrossCorrImgPath + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        Start_CrossCorrImgPath[i1] = (tp1 + initial_array_col_size * i1);

	tp1 = (long  int *)(selfcorr_chan1_complex + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        selfcorr_chan1_complex[i1] = (tp1 + initial_array_col_size * i1);

	tp1 = (long  int *)(selfcorr_chan2_complex + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
       selfcorr_chan2_complex[i1] = (tp1 + initial_array_col_size * i1);

	tp1 = (long  int *)(real_crosscorr_complex  + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        real_crosscorr_complex [i1] = (tp1 + initial_array_col_size * i1);

	tp1 = (long  int *)(img_crosscorr_complex + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        img_crosscorr_complex[i1] = (tp1 + initial_array_col_size * i1);

	tp1 = (long  int *)(before_reorder_selfcorr1 + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        before_reorder_selfcorr1[i1] = (tp1 + initial_array_col_size * i1);

	tp1 = (long  int *)(reordered_selfcorr1 + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        reordered_selfcorr1[i1] = (tp1 + initial_array_col_size * i1);

	tp1 = (long  int *)(before_reorder_selfcorr2 + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        before_reorder_selfcorr2[i1] = (tp1 + initial_array_col_size * i1);

	tp1 = (long  int *)(reordered_selfcorr2 + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        reordered_selfcorr2[i1] = (tp1 + initial_array_col_size * i1);

	tp1 = (long  int *)(before_reorder_real_crosscorr + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        before_reorder_real_crosscorr[i1] = (tp1 + initial_array_col_size * i1);

	tp1 = (long  int *)(real_reordered_crosscorr + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        real_reordered_crosscorr[i1] = (tp1 + initial_array_col_size * i1);

	tp1 = (long  int *)(before_reorder_img_crosscorr + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        before_reorder_img_crosscorr[i1] = (tp1 + initial_array_col_size * i1);

	tp1 = (long  int *)(img_reordered_crosscorr + Num_FirmwareBuffers);
	for(i1 = 0; i1 < Num_FirmwareBuffers; i1++)
        img_reordered_crosscorr[i1] = (tp1 + initial_array_col_size * i1);

	double temp_sum,temp_selfcorr,real_crosscorr,img_crosscorr;

    const char version[30]="saras3_acq_v1: 13FEB18";
    char outfile[70],buf[20];
	char hostname[]="xport11";
	char command1[200],command2[200],command3[100];
	float temperature;
	temperature = 0;
	struct termios toptions;
	struct timeval timeout;      
	timeout.tv_sec = 5;
    	timeout.tv_usec = 0;
    	
	// Miriad-related variables
	char source_name[9];
	char velocity_type[9] = {'V','E','L','O','-','O','B','S','\0'};
	int ispec;
	int fname_length;
	int cnumber;
	int var_ivalue[1];
	static int npoints,nn;
	int antenna1,antenna2,antenna3;
	static int flags[8193];
	int access_result;
	float baseline_value[1];
	double preamble[4];
	double p1,p2,p3;
	double ant_az[3],ant_el[3];
	double freq_channel1[1];
	double freq_inc[1];
	double time_var[1];
	double coord_var[2];
	double site_latitude[1],site_longitude[1],longitude_radians;
	static float data[16380];
	float var_veldop[1];
	float var_vsource[1];
	double var_restfreq[1];
	double sra[1],sdec[1];
	double lo1[1],lo2[1],freq[1],freqif[1];
	int mount[1];
	float evector[1];
	int nnpol,npol[1];
	float jyperk[1],inttime[1],epoch[1];
	double antpos[9];
	float tpower[1];
	float wfreq[1],wwidth[1];
	int time_info[6][16];
	int time_info1[6];
    	long int jjdd,yyyy,mmmm,dddd;
    	double julian_date;
	double lst;
	float old_time,old_day,old_year;
	float current_time,current_day,current_year;
	
	int data_size, header_size,sze=0,oldbuf;//17907712
	int oldlen = sizeof(int);
    	struct sockaddr_in cliaddr,servaddr;
	socklen_t cliaddr_size;
    	int sock_raw;
	unsigned short iphdrlen;
	
	    
// copied subroutine state_sw_rpi block here above main code. Since setup_rpi was being called everytime in this code, and there all pins were set
// high, memory of previous state was not held. Commented out the setting pins high in setup_rpi block of subroutines.c - NS, MSR, Vani and BSG 22 july 2024		
    for(r=0;r<4;r++)
    {
      state_sw_rpi_vna(pins,num_of_int,source_name,temperature);
       
    }
    //state_sw_rpi_vna(pins)
		printf(" %s Int %6d of %6d state:%2d ",source_name,inint,nint,inint%6);
	 	
		usleep(200000);  //NS made it 200ms from 1sec on 21 july 2024, ori 100 ms sleep time to let switches settle
		
	FILE *file= fopen("state_name.txt", "w");
		int results = fputs(source_name,file);
		if(results==EOF) printf("Error writing state_name.txt\n");
		
		fclose(file);	

	    
    }
  





















