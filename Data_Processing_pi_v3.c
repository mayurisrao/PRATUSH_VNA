/* * saras3_acq_v4.c 8June 2018
 *
 * Acquire UTC from the GPS, 
 * and write out a MIRIAD dataset
 
 *	
 * 17Sep14 PC time use; GPS time not considered
 * 15Dec14 Setting switch states included
 * Change from v9 : removed sleep
 * 10June15 get time using only ftime; open/close output file for every successful data record
 *
 * 13Feb2018 : rename saras2_acq_vf2_16k.c to saras3_acq_v1.c
 *             change controls and state cycles from 4 to 6 to include
 *             "dicky" switch at front end, cal on/off, optical switch
 * 20Feb2018 : change from v1 to v2. v2 version is for three control lines.
 *             one for optical switch at base station.
 *             two for noise cal and dicky switch at antenna base.
 * 17Apr2018 : change from v2 to v3. 
		the new switch+LNA 

 * 8June2018 : change from v3 to v4. 
 * This program is used to acquire data from 2x8192 FFT firmware(saras2_v9_bnw_fft16k_2_Working6June2018_1648hrs.bin). 
 * FPGA firmware was modified from 8x2048 point FFt to 2x8192 point FFT. Earlier, the 8-point parallel FFT gave output 
 * in bit reversed order. In the 2x8192 point architecture, only one half of data(16384 points in the FFT) is brought 
 * out and is in normal order. In this code , at the place where data is stitched to obtain 16384 points, mapping is 
 * changed to reflect the normal order FFt output- 
 
*/
//
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
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

#define SIZE 256
#define PI 3.14159265358979

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
const int M=8;                        				// Number of parallel, pipelined N-point FFTs 
const int N=2048;                     				// Length of each pipelined FFT
size_t count=0;
int tno,l,data_ind=1, flag=0, npkt=16412, dpkt, start=0, stop=0,len,next;
long int zero_len=10, pktsize=1024, start_ind=0, stop_ind=0;

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

int main(int argc, char *argv[])
{ 
  	long int i,k,j,ii,jj,zz,frame=0,n;
  	int SelfCorrPattern,CrossCorrPattern;
	int chan1_path[8] = {17,33,49,65,81,97,113,129};
	int chan2_path[8] = {18,34,50,66,82,98,114,130};
	int cc_real[8]    = {19,35,51,67,83,99,115,131};
	int cc_img[8]    = {20,36,52,68,84,100,116,132};
	int chan1_ind[8]  = {0,0,0,0,0,0,0,0};
	int chan2_ind[8] = {0,0,0,0,0,0,0,0};
	int cc_real_ind[8] = {0,0,0,0,0,0,0,0};
	int cc_img_ind[8] = {0,0,0,0,0,0,0,0};
	
	static long int Start_AutoCorr_Chan1[8][32774],Start_AutoCorr_Chan2[8][32774],
			Start_CrossCorrRealPath[8][32774],
			Start_CrossCorrImgPath[8][32774];
	static double selfcorr_chan1_complex[8][32774],selfcorr_chan2_complex[8][32774];
	static double real_crosscorr_complex[8][32774],img_crosscorr_complex[8][32774];
	static double before_reorder_selfcorr1[8][32774],reordered_selfcorr1[8][32774];
	static double before_reorder_selfcorr2[8][32774],reordered_selfcorr2[8][32774];
	static double before_reorder_real_crosscorr[8][32774],real_reordered_crosscorr[8][32774];
	static double before_reorder_img_crosscorr[8][32774],img_reordered_crosscorr[8][32774];
	static double final_selfcorr1[262152],final_selfcorr2[262152],final_real_crosscorr[262152],
			final_img_crosscorr[262152];
	static double selfcorr1_avg[262152],selfcorr2_avg[262152],crosscorr_ravg[262152],
			crosscorr_iavg[262152];
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
	char source_name[5];
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
	
	int data_size, header_size,sze=0,rcvbuf=16859136,oldbuf;//17907712
	int oldlen = sizeof(int);
    	struct sockaddr_in cliaddr,servaddr;
	socklen_t cliaddr_size;
    	int sock_raw;
	unsigned short iphdrlen;

	char ncal1_state,psw_state,optsw_state,pin;
	int inint,nint,nint4,fa,ct=1,p;
	char nint_buf[30];
	char input_data[6];

	FILE *ptr;

	/* Arduino presets */
	/*fa = open("/dev/ttyACM0",O_RDWR | O_NOCTTY);
	if (fa == -1) 
	{
		perror("Unable to open port for Arduino\n");
		return -1;
	}
*/
//--------------------------------------------------------------	
/* CHECK 
 	tcgetattr(fa, &toptions);
	cfsetispeed(&toptions, B9600);
	cfsetospeed(&toptions, B9600);
	toptions.c_cflag &= ~PARENB;
	toptions.c_cflag &= ~CSTOPB;
	toptions.c_cflag &= ~CSIZE;
	toptions.c_cflag |= CS8;
	toptions.c_lflag |= ICANON;
	tcsetattr(fa, TCSANOW, &toptions);
*/ 
//--------------------------------------------------------------	
	/*query_gps();		//Query GPS for time.....commented
	time_info[0]=utc_hh;
	time_info[1]=utc_mm;
	time_info[2]=utc_ss;
	time_info[3]=utc_day;
	time_info[4]=utc_month;
	time_info[5]=utc_year;
	sprintf(outfile,"%04d-%02d-%02d_%02d%02d%02d.dat%c",
	time_info[5],time_info[4],time_info[3],
	time_info[0],time_info[1],time_info[2],'\0');*/
	
						//Query system time
/*	ftime(&cur_time_struct2);
	cur_time_long = cur_time_struct2.time;
  	cur_time_struct = (struct tm *) localtime(&cur_time_long);
	time_info1[0]=cur_time_struct->tm_hour;
	time_info1[1]=cur_time_struct->tm_min;
	time_info1[2]=cur_time_struct->tm_sec;
	time_info1[3]=cur_time_struct->tm_mday;
	time_info1[4]=cur_time_struct->tm_mon+1;
	time_info1[5]=cur_time_struct->tm_year + 1900;
	sprintf(outfile,"%04d-%02d-%02d_%02d%02d%02d.dat%c",
		  time_info1[5],time_info1[4],time_info1[3],
		  time_info1[0],time_info1[1],time_info1[2],'\0');
  		
	// Setup parameters for writing the output miriad data file */

	// set all flags to good 

	
	/* Open output vis file   
	fprintf(stderr,"Open file with name: %s \n",outfile);
    
	uvopen_c(&tno,outfile,"new");
	hisopen_c(tno,"write");

	/* setup the output vis file 
	wrhda_c(tno,"obstype","crosscorrelation");
	uvputvra_c(tno,"source","zenith sky");
	uvputvra_c(tno,"operator","eor");
	uvputvra_c(tno,"version",version);
	sra[0]=0.0;
	sdec[0]=0.0;
	uvputvrd_c(tno,"ra",sra,1);
	uvputvrd_c(tno,"obsra",sra,1);
	uvputvrd_c(tno,"dec",sdec,1);
	uvputvrd_c(tno,"obsdec",sdec,1);
	lo1[0]=0.250;
	lo2[0]=0.0;
	freq[0]=0.125;
	freqif[0]=0.0;
	uvputvrd_c(tno,"lo1",lo1,1);
	uvputvrd_c(tno,"lo2",lo2,1);
	uvputvrd_c(tno,"freq",freq,1);
	uvputvrd_c(tno,"freqif",freqif,1);
	mount[0]=0;
	evector[0]=0.0;
	uvputvri_c(tno,"mount", mount, 1);
	uvputvrr_c(tno,"evector",evector,1);
	uvputvrr_c(tno,"chi",evector,1);
	uvputvra_c(tno,"telescop","eor");
	jyperk[0]=1.0;
	uvputvrr_c(tno,"jyperk",jyperk,1);
	inttime[0]=1.0;
	uvputvrr_c(tno,"inttime",inttime,1);
	epoch[0]=2000.0;
	uvputvrr_c(tno,"epoch",epoch,1);
	nnpol=1;
	wrhdi_c(tno,"npol",nnpol);
	antpos[0]=0.0;
	antpos[1]=1.0;
	antpos[2]=2.0;
	antpos[3]=0.0;
	antpos[4]=0.0;
	antpos[5]=0.0;
	antpos[6]=0.0;
	antpos[7]=0.0;
	antpos[8]=0.0;
	uvputvrd_c(tno,"antpos",antpos,9);
	uvputvrd_c(tno,"time",time_var,1);
	uvputvrd_c(tno,"ut",time_var,1);
	nn=0;
	p1=0.0;
	p2=0.0;
	p3=0.0;
	uvset_c(tno,"corr","r",nn,p1,p2,p3);  

	/* write floats and not scaled integers 
	var_ivalue[0]=3;
	uvputvri_c(tno,"nants",var_ivalue,1);
	var_ivalue[0]=8193;
	uvputvri_c(tno,"nchan",var_ivalue,1);
	var_ivalue[0]=1;
	uvputvri_c(tno,"npol",var_ivalue,1);
	var_ivalue[0]=1;
	uvputvri_c(tno,"nspect",var_ivalue,1);
	var_ivalue[0]=-1;
	uvputvri_c(tno,"pol",var_ivalue,1);
	var_ivalue[0]=8193;
	uvputvri_c(tno,"nschan",var_ivalue,1);
	var_ivalue[0]=1;
	uvputvri_c(tno,"ischan",var_ivalue,1);
	var_ivalue[0]=1;
	uvputvri_c(tno,"ntpower",var_ivalue,1);
	var_ivalue[0]=0;
	uvputvri_c(tno,"nwide",var_ivalue,1);
	
	tpower[0]=1.0;
	uvputvrr_c(tno,"tpower",tpower,1);
	ant_az[0]=0.0;
	ant_az[1]=0.0;
	ant_az[2]=0.0;
	ant_el[0]=90.0;
	ant_el[1]=90.0;
	ant_el[2]=90.0;
	uvputvrd_c(tno,"antaz",ant_az,3);
	uvputvrd_c(tno,"antel",ant_el,3);
	var_veldop[0]=0.0;
	uvputvrr_c(tno,"veldop",var_veldop,1);
	var_vsource[0]=0.0;
	uvputvrr_c(tno,"vsource",var_vsource,1);
	var_restfreq[0]=0.0;
	uvputvrd_c(tno,"restfreq",var_restfreq,1);
	freq_channel1[0]=0.0; /* GHz 
	uvputvrd_c(tno,"sfreq",freq_channel1,1);
	freq_inc[0]= 3.0517578125e-05; /* GHz 
	uvputvrd_c(tno,"sdf",freq_inc,1);
	site_latitude[0] = (double)(14.2423277777777778 * PI/180.0);
	uvputvrd_c(tno,"latitud",site_latitude,1);
	site_longitude[0] = (double)(77.61260555555555556 * PI/180.0);
	uvputvrd_c(tno,"longitu",site_longitude,1);
	antenna1=1;
	antenna2=2;
	baseline_value[0]=(float)(256*antenna1+antenna2);
	uvputvrr_c(tno,"baseline",baseline_value,1);
	coord_var[0]=0.0;
	coord_var[1]=0.0;
	uvputvrd_c(tno,"coord",coord_var,2);
	uvputvr_c(tno,1,"veltype",velocity_type,8);	

	// Close output files
	hisclose_c(tno);
	uvclose_c(tno);
*/



	for(i=0;i<8193;++i) flags[i]=1;

	npoints=8193; 

	/* Allocate a buffer to hold the incoming UDP packet */
	unsigned char *buffer = (unsigned char *) malloc(1024);
	//unsigned char *pkt_ctr = (unsigned char *) malloc(10);
	
	/* Allocate a buffer to hold the useful data from all UDP packets */
	if ((stage=calloc (npkt,pktsize)) == NULL)
  	{ perror ("calloc"); return -1; }

	/* Allocate a buffer to hold headerless data */
	dpkt = npkt/2;
//	if ((chan_data=calloc (dpkt,pktsize)) == NULL)
//	{ perror ("calloc"); return -1; }

//	if ((chan_data=calloc (npkt*pktsize,sizeof(unsigned char))) == NULL)
	if ((chan_data=calloc (dpkt,pktsize)) == NULL)

	{ perror ("calloc"); return -1; }

	  if (temperature < 40)
	  {

		/* Acquisition routine starts from here */
		memset (stage,0,sizeof(stage));
		memset (chan_data,0,sizeof(chan_data));
		


	long Size_var;
    


	//unsigned char* temp_data= (unsigned char*)calloc(npkt*pktsize, sizeof(unsigned char));
	//unsigned char* chan_datain= (unsigned char*)calloc((npkt*pktsize), sizeof(unsigned char));
	unsigned char* chan_datain= calloc (npkt,pktsize);
	unsigned char* temp_data= calloc (npkt,pktsize);



//--------------------------------------------------------------------
    FILE *ptr_sourcename = fopen("state_name.txt", "r");

    char code[10];
    char c;
    flag=0;
    fscanf(ptr_sourcename,"%s",source_name);
    //fprintf(stderr,"CODE: %s \n",code);
    fclose(ptr_sourcename);
    
    FILE *ptr_filename = fopen("MiriadFilename.txt", "rt");

    fscanf(ptr_filename,"%s",outfile);
//    fprintf(stderr,"MiriadFilename: %s \n",outfile);
    fclose(ptr_filename);
    


	ptr = fopen("Extracted_data.dat","rb");
        fseek(ptr,190,SEEK_SET);    

	/* for(i = 0; i<npkt*pktsize; i++)
	{
		chan_datain[i]=temp_data[i+190]; 
		//printf("%x---%x\n",chan_datain[i],temp_data[i+190]);
	}
	fclose(ptr);
	*/	

	unsigned int NumOfDataPointsToRead= 1024 ,data_size;

		
	    while(ct <= 16380) 
	    {
    			memset (buffer,0,sizeof(buffer));			
		        fseek(ptr,34+74,SEEK_CUR);    
			fread(buffer,NumOfDataPointsToRead,sizeof(unsigned char),ptr);
 
//		   for (i=0;i<1024;i++)
//			printf("buffer %x %x\n", buffer[i], stage[i]); 
				if((ct%1024 == 0 || ct == 1 ))  // if at the beginning of a new frame
				{
				//query_gps();		//Query GPS for time....currently commented
				//time_info[0][frame]=utc_hh;
				//time_info[1][frame]=utc_mm;
				//time_info[2][frame]=utc_ss;
				//time_info[3][frame]=utc_day;
				//time_info[4][frame]=utc_month;
				//time_info[5][frame]=utc_year;
									//Query system time.....currently used
				ftime(&cur_time_struct2);
				cur_time_long = cur_time_struct2.time;
				millitime=cur_time_struct2.millitm;
				cur_time_struct = (struct tm *) localtime(&cur_time_long);
				time_info[0][frame]=cur_time_struct->tm_hour;
				time_info[1][frame]=cur_time_struct->tm_min;
				time_info[2][frame]=cur_time_struct->tm_sec;
				time_info[3][frame]=cur_time_struct->tm_mday;
				time_info[4][frame]=cur_time_struct->tm_mon+1;
				time_info[5][frame]=cur_time_struct->tm_year + 1900;
				timesec[frame] = (float)cur_time_struct->tm_sec + (float)millitime/1000.0;

				frame++;
				}
				
				next = (ct-1)*pktsize;  // N=1024
				memcpy(stage+next, buffer, pktsize);
				
				ct = ct+1;

	//		for (i=0;i<1024;i++)
	//		printf("buffer %x %x\n", buffer[i], stage[i]); 
		
	}
			
	fclose(ptr);

	 
		// Reorganising data by removing byte stuffing
                for (ii=1,jj=0; ii<(npkt*pktsize); ii+=2,jj++)
		{
                        chan_data[jj] = stage[ii];
			//printf("%x--%x\n",stage[ii],chan_data[jj]);
			
                }


		len = npkt*pktsize;
                SelfCorrPattern  = 172;	// 0xAC
                CrossCorrPattern = 204; // 0xCC

                for (ii=1;ii<(len/2);ii++)
                {	
                        if(chan_data[ii] == SelfCorrPattern)			 //If data corresponds to autocorrelation buffer
                        {
                                for(jj=0;jj<M;jj++)
                                {
                                        if (chan_data[ii-1] == chan1_path[jj])   //If AC data corresponds to Channelizer #1 
                                        {
                                                if (((chan_data[ii+8] == 172) || (chan_data[ii+8] == 204))
                                                        && ((chan_data[ii+16] == 172) || (chan_data[ii+16] == 204))
							&& ((chan_data[ii+24] == 172) || (chan_data[ii+24] == 204))
							&& ((chan_data[ii+32] == 172) || (chan_data[ii+32] == 204)))
                                                {
                                                        Start_AutoCorr_Chan1[jj][chan1_ind[jj]] = ii+1;
                                                        chan1_ind[jj] = chan1_ind[jj]+1;
                                                }
                                        }
                                        else if (chan_data[ii-1] == chan2_path[jj])   //If AC data corresponds to Channelizer #2
                                        {
                                                if (((chan_data[ii+8] == 172) || (chan_data[ii+8] == 204))
                                                       && ((chan_data[ii+16] == 172) || (chan_data[ii+16] == 204))
							&& ((chan_data[ii+24] == 172) || (chan_data[ii+24] == 204))
							&& ((chan_data[ii+32] == 172) || (chan_data[ii+32] == 204)))

                                                {
                                                        Start_AutoCorr_Chan2[jj][chan2_ind[jj]] = ii+1;
                                                        chan2_ind[jj] = chan2_ind[jj]+1;
                                                }
                                        }
                                }
                        }
                        else if(chan_data[ii] == CrossCorrPattern)		//If data corresponds to crosscorrelation buffer
                        {
                                for(jj=0;jj<M;jj++)
                                {
                                        if (chan_data[ii-1] == cc_real[jj])   	//If CC data corresponds to REAL  
                                        {
                                                if (((chan_data[ii+8] == 172) || (chan_data[ii+8] == 204))
                                                      && ((chan_data[ii+16] == 172) || (chan_data[ii+16] == 204))
							&& ((chan_data[ii+24] == 172) || (chan_data[ii+24] == 204))
							&& ((chan_data[ii+32] == 172) || (chan_data[ii+32] == 204)))
						      	
                                                {
                                                        Start_CrossCorrRealPath[jj][cc_real_ind[jj]] = ii+1;
                                                        cc_real_ind[jj] = cc_real_ind[jj]+1;
                                                }
                                        }
                                        else if (chan_data[ii-1] == cc_img[jj])   	//If CC data corresponds to IMG 
                                        {
                                                if (((chan_data[ii+8] == 172) || (chan_data[ii+8] == 204))
                                                       && ((chan_data[ii+16] == 172) || (chan_data[ii+16] == 204))
							&& ((chan_data[ii+24] == 172) || (chan_data[ii+24] == 204))
							&& ((chan_data[ii+32] == 172) || (chan_data[ii+32] == 204)))
						       
                                                {
                                                        Start_CrossCorrImgPath[jj][cc_img_ind[jj]] = ii+1;
                                                        cc_img_ind[jj] = cc_img_ind[jj]+1;

                                                }
                                        }
                                }
                        }
                }

		/*--------------------------------------------------------------------------
                ---------- Stiching together Channelizer data - BEGINS HERE-----------------
                --------------------------------------------------------------------------*/

                if(chan1_ind[0] > N)
                {
		  for(ii=0;ii<(32774);ii++) //Mayuri 27 June 2017
                        {
                                /***********************************************************************
                                ----Begin stitching together data corresponding to SelfCorr, Chan #1----
                                ***********************************************************************/

                                for(jj=0;jj<M;jj++)
                                {
                                        temp = Start_AutoCorr_Chan1[jj][ii];
                                        temp_sum = (double) (( chan_data[temp+4]) * pow(2,32)) + 
                                                            (( chan_data[temp+3]) * pow(2,24)) + 
                                                            (( chan_data[temp+2]) * pow(2,16)) + 
                                                            (( chan_data[temp+1]) * pow(2,8)) +  
                                                            (chan_data[temp]);	

                                        if(((chan_data[temp+5])) < 128 ) // number is positive
                                                temp_selfcorr = (double)  ((chan_data[temp+5]) * pow(2,40)) + 	temp_sum;
                                        else if (((chan_data[temp+5])) >= 128 ) // number is negative
                                                temp_selfcorr = (double) (-128 * pow(2,40)) + 
                                                                        (((chan_data[temp+5])-128) * pow(2,40)) + temp_sum;
                                        selfcorr_chan1_complex[jj][ii]= temp_selfcorr;

                                        temp = 0;
                                        temp_sum = 0;
                                        temp_selfcorr = 0;
                                }

                                /***********************************************************************
                                ----Begin stitching together data corresponding to SelfCorr, Chan #2----
                                ***********************************************************************/

                                for(jj=0;jj<M;jj++)
                                {
                                        temp = Start_AutoCorr_Chan2[jj][ii];
                                        temp_sum = (double) (( chan_data[temp+4]) * pow(2,32)) + 
                                                            (( chan_data[temp+3]) * pow(2,24)) + 
                                                            (( chan_data[temp+2]) * pow(2,16)) + 
                                                            (( chan_data[temp+1]) * pow(2,8)) +  
                                                            (chan_data[temp]);	

                                        if(((chan_data[temp+5])) < 128 ) // number is positive
                                                temp_selfcorr = (double)  ((chan_data[temp+5])*pow(2,40)) + temp_sum;
                                        else if (((chan_data[temp+5])) >= 128 ) // number is negative
                                                temp_selfcorr = (double) (-128*pow(2,40)) + 
                                                                                         (((chan_data[temp+5])-128)*pow(2,40)) + temp_sum;
                                        selfcorr_chan2_complex[jj][ii]= temp_selfcorr;

                                        temp = 0;
                                        temp_sum = 0;
                                        temp_selfcorr = 0;
                                }
                                //printf("self corr chan2 done\n");

                                /***********************************************************************
                                --------Begin stitching together data corresponding to CrossCorr--------
                                ***********************************************************************/

                                for(jj=0;jj<M;jj++)
                                {
                                        temp = Start_CrossCorrImgPath[jj][ii]; //picking-up starting address of IMG-PART 
                                        temp_sum = (double) (( chan_data[temp+4]) * pow(2,32)) + 
                                                            (( chan_data[temp+3]) * pow(2,24)) + 
                                                            (( chan_data[temp+2]) * pow(2,16)) +  
                                                            (( chan_data[temp+1]) * pow(2,8)) +
                                                            (chan_data[temp]);		

                                        if(((chan_data[temp+5])) < 128 ) // number is positive
                                                img_crosscorr = (double) ((chan_data[temp+5])*pow(2,40)) + temp_sum;
                                        else if (((chan_data[temp+5])) >= 128 ) // number is negative
                                                img_crosscorr = (double) (-128*pow(2,40)) + 
                                                                         (((chan_data[temp+5])-128)*pow(2,40)) + temp_sum;

                                        temp = 0;
                                        temp_sum = 0;

                                        temp = Start_CrossCorrRealPath[jj][ii]; //picking-up starting address of REAL-PART
                                        temp_sum = (double) ((chan_data[temp+4]) * pow(2,32)) + 
                                                            ((chan_data[temp+3]) * pow(2,24)) + 
                                                            ((chan_data[temp+2]) * pow(2,16)) +  							    ((chan_data[temp+1]) * pow(2,8)) +  
                                                            (chan_data[temp]);		

                                        if(((chan_data[temp+5])) < 128 ) // number is positive
                                                real_crosscorr = (double) ((chan_data[temp+5])*pow(2,40)) + temp_sum;
                                        else if (((chan_data[temp+5])) >= 128 ) // number is negative
                                                real_crosscorr = (double) (-128*pow(2,40)) + 
                                                                  (((chan_data[temp+5])-128)*pow(2,40)) + temp_sum;

                                        real_crosscorr_complex[jj][ii] = real_crosscorr;
                                        img_crosscorr_complex[jj][ii] = img_crosscorr;						

                                        //crosscorr_complex[jj][ii]= real_crosscorr + img_crosscorr * _Complex_I;

                                        temp = 0;
                                        temp_sum = 0;
                                        img_crosscorr = 0;
                                        real_crosscorr = 0;
                                }
                        }
                }
                else
                {
                        fprintf(stdout,"Markers & Patterns NOT found\n");
                }

                /*--------------------------------------------------------------------------
                -----------Reordering of Parallel FFT data - BEGINS here--------------------
                --------------------------------------------------------------------------*/

                //Is the mapping for output file from GigE for Channelizer-1
                for(ii=0;ii<(32774);ii++) //Mayuri 27 Jun 2017
					  // 8 June 2018 Normal order FFt mapping
                {
                        before_reorder_selfcorr1[0][ii] = selfcorr_chan1_complex[0][ii];
                        before_reorder_selfcorr1[1][ii] = selfcorr_chan1_complex[1][ii];
                        before_reorder_selfcorr1[2][ii] = selfcorr_chan1_complex[2][ii];
                        before_reorder_selfcorr1[3][ii] = selfcorr_chan1_complex[3][ii];
                        before_reorder_selfcorr1[4][ii] = selfcorr_chan1_complex[4][ii];
                        before_reorder_selfcorr1[5][ii] = selfcorr_chan1_complex[5][ii];
                        before_reorder_selfcorr1[6][ii] = selfcorr_chan1_complex[6][ii];
                        before_reorder_selfcorr1[7][ii] = selfcorr_chan1_complex[7][ii];
                        reordered_selfcorr1[0][ii] = before_reorder_selfcorr1[0][ii];
                        reordered_selfcorr1[1][ii] = before_reorder_selfcorr1[1][ii];
                        reordered_selfcorr1[2][ii] = before_reorder_selfcorr1[2][ii];
                        reordered_selfcorr1[3][ii] = before_reorder_selfcorr1[3][ii];
                        reordered_selfcorr1[4][ii] = before_reorder_selfcorr1[4][ii];
                        reordered_selfcorr1[5][ii] = before_reorder_selfcorr1[5][ii];
                        reordered_selfcorr1[6][ii] = before_reorder_selfcorr1[6][ii];
                        reordered_selfcorr1[7][ii] = before_reorder_selfcorr1[7][ii];
			
                }

                //Is the mapping for output file from GigE for Channelizer-2			
                for(ii=0;ii<(32774);ii++) // Mayuri 27 Jun 2017
					// 8 June 2018 Normal order FFt mapping	
                {
                        before_reorder_selfcorr2[0][ii] = selfcorr_chan2_complex[0][ii];
                        before_reorder_selfcorr2[1][ii] = selfcorr_chan2_complex[1][ii];
                        before_reorder_selfcorr2[2][ii] = selfcorr_chan2_complex[2][ii];
                        before_reorder_selfcorr2[3][ii] = selfcorr_chan2_complex[3][ii];
                        before_reorder_selfcorr2[4][ii] = selfcorr_chan2_complex[4][ii];
                        before_reorder_selfcorr2[5][ii] = selfcorr_chan2_complex[5][ii];
                        before_reorder_selfcorr2[6][ii] = selfcorr_chan2_complex[6][ii];
                        before_reorder_selfcorr2[7][ii] = selfcorr_chan2_complex[7][ii];
                        reordered_selfcorr2[0][ii] = before_reorder_selfcorr2[0][ii];
                        reordered_selfcorr2[1][ii] = before_reorder_selfcorr2[1][ii];
                        reordered_selfcorr2[2][ii] = before_reorder_selfcorr2[2][ii];
                        reordered_selfcorr2[3][ii] = before_reorder_selfcorr2[3][ii];
                        reordered_selfcorr2[4][ii] = before_reorder_selfcorr2[4][ii];
                        reordered_selfcorr2[5][ii] = before_reorder_selfcorr2[5][ii];
                        reordered_selfcorr2[6][ii] = before_reorder_selfcorr2[6][ii];
                        reordered_selfcorr2[7][ii] = before_reorder_selfcorr2[7][ii];
                }

                //Is the mapping for output file from GigE for Cross-Correlation
                for(ii=0;ii<(32774);ii++) // Mayuri 27 Jun 2017--   
					  // 8 June 2018 Normal order FFt mapping
                {
                        before_reorder_real_crosscorr[0][ii] = real_crosscorr_complex[0][ii];
                        before_reorder_real_crosscorr[1][ii] = real_crosscorr_complex[1][ii];
                        before_reorder_real_crosscorr[2][ii] = real_crosscorr_complex[2][ii];
                        before_reorder_real_crosscorr[3][ii] = real_crosscorr_complex[3][ii];
                        before_reorder_real_crosscorr[4][ii] = real_crosscorr_complex[4][ii];
                        before_reorder_real_crosscorr[5][ii] = real_crosscorr_complex[5][ii];
                        before_reorder_real_crosscorr[6][ii] = real_crosscorr_complex[6][ii];
                        before_reorder_real_crosscorr[7][ii] = real_crosscorr_complex[7][ii];

                        real_reordered_crosscorr[0][ii] = before_reorder_real_crosscorr[0][ii];
                        real_reordered_crosscorr[1][ii] = before_reorder_real_crosscorr[1][ii];
                        real_reordered_crosscorr[2][ii] = before_reorder_real_crosscorr[2][ii];
                        real_reordered_crosscorr[3][ii] = before_reorder_real_crosscorr[3][ii];
                        real_reordered_crosscorr[4][ii] = before_reorder_real_crosscorr[4][ii];
                        real_reordered_crosscorr[5][ii] = before_reorder_real_crosscorr[5][ii];
                        real_reordered_crosscorr[6][ii] = before_reorder_real_crosscorr[6][ii];
                        real_reordered_crosscorr[7][ii] = before_reorder_real_crosscorr[7][ii];

                        before_reorder_img_crosscorr[0][ii] = img_crosscorr_complex[0][ii];
                        before_reorder_img_crosscorr[1][ii] = img_crosscorr_complex[1][ii];
                        before_reorder_img_crosscorr[2][ii] = img_crosscorr_complex[2][ii];
                        before_reorder_img_crosscorr[3][ii] = img_crosscorr_complex[3][ii];
                        before_reorder_img_crosscorr[4][ii] = img_crosscorr_complex[4][ii];
                        before_reorder_img_crosscorr[5][ii] = img_crosscorr_complex[5][ii];
                        before_reorder_img_crosscorr[6][ii] = img_crosscorr_complex[6][ii];
                        before_reorder_img_crosscorr[7][ii] = img_crosscorr_complex[7][ii];

                        img_reordered_crosscorr[0][ii] = before_reorder_img_crosscorr[0][ii];
                        img_reordered_crosscorr[1][ii] = before_reorder_img_crosscorr[1][ii];
                        img_reordered_crosscorr[2][ii] = before_reorder_img_crosscorr[2][ii];
                        img_reordered_crosscorr[3][ii] = before_reorder_img_crosscorr[3][ii];
                        img_reordered_crosscorr[4][ii] = before_reorder_img_crosscorr[4][ii];
                        img_reordered_crosscorr[5][ii] = before_reorder_img_crosscorr[5][ii];
                        img_reordered_crosscorr[6][ii] = before_reorder_img_crosscorr[6][ii];
                        img_reordered_crosscorr[7][ii] = before_reorder_img_crosscorr[7][ii];
                }		

				// If no keyboard hit then write all 16 frames in output file.	

                if(kbhit() == 0)
                {

				// Open output files in append mode
				uvopen_c(&tno,outfile,"append");
				hisopen_c(tno,"append");

				// write the header record here with source name
				uvputvr_c(tno,1,"source",source_name,5);


                for(frame=0;frame<16;frame++)
                {		

					start=0;
					for(ii=0;ii<M;ii++)
					{			
							stop  = start+(N-1);
							for(jj=start,zz=(0+(frame*N));(jj<(stop+1) && zz<(N+(frame*N)));jj++,zz++)
							{
									final_selfcorr1[jj] = reordered_selfcorr1[ii][zz];
									final_selfcorr2[jj] = reordered_selfcorr2[ii][zz];
									final_real_crosscorr[jj] = real_reordered_crosscorr[ii][zz];
									final_img_crosscorr[jj] = img_reordered_crosscorr[ii][zz];

									selfcorr1_avg[jj] = final_selfcorr1[jj]/2048; //Mayuri 27 Jun 2017
									selfcorr2_avg[jj] = final_selfcorr2[jj]/2048; //Mayuri 27 Jun 2017
									crosscorr_ravg[jj] = final_real_crosscorr[jj]/2048; //Mayuri 27 Jun 2017
									crosscorr_iavg[jj] = final_img_crosscorr[jj]/2048; //Mayuri 27 Jun 2017
//									printf("here-%x\n",final_real_crosscorr[jj]);

							}
							start = stop+1;	
					}
										//printf("here-%d\n",frame);

					preamble[0]=0.0;  /* u coordinate */
					preamble[1]=0.0;  /* v coordinate */
	
					// assemble the current JD in preamble[2] from the array time_info that contains UTC
					yyyy=time_info[5][frame];
					mmmm=time_info[4][frame];
					dddd=time_info[3][frame];
					jjdd = ( 1461 * ( yyyy + 4800 + ( mmmm - 14 ) / 12 ) ) / 4 +
							( 367 * ( mmmm - 2 - 12 * ( ( mmmm - 14 ) / 12 ) ) ) / 12 -
							( 3 * ( ( yyyy + 4900 + ( mmmm - 14 ) / 12 ) / 100 ) ) / 4 +
					dddd - 32075;
					julian_date = (double)jjdd -0.5;
					julian_date += (double)timesec[frame]/(3600.0*24.0) + 
							(double)time_info[1][frame]/(60.0*24.0) + (double)time_info[0][frame]/24.0;
					preamble[2] = julian_date;
	
					longitude_radians = (double)site_longitude[0];

								//	lst = cal_lst(julian_date, longitude_radians);


									time_var[0] = lst;

					antenna1=1;
					antenna2=1;
					preamble[3]=(double)(256*antenna1+antenna2);

					// write the data record here
					for(i=0;i<8193;++i) //Mayuri 27 Jun 2017
					{
							data[2*i]=(float)selfcorr1_avg[i];
							data[2*i+1]=0.0;
					}
				
	
					uvputvrd_c(tno,"lst",time_var,1);
					uvwrite_c(tno,preamble,data,flags,npoints);
	
					antenna1=2;	
					antenna2=2;
					preamble[3]=(double)(256*antenna1+antenna2);
					for(i=0;i<8193;++i) //Mayuri 27 Jun 2017
					{
							data[2*i]=(float)selfcorr2_avg[i];
							data[2*i+1]=0.0;
					}
	
					uvputvrd_c(tno,"lst",time_var,1);                                
					uvwrite_c(tno,preamble,data,flags,npoints);
	
					antenna1=1;
					antenna2=2;
					preamble[3]=(double)(256*antenna1+antenna2);
					for(i=0;i<8193;++i) //Mayuri 27 Jun 2017
					{
							data[2*i]=(float)crosscorr_ravg[i];
							data[2*i+1]=(float)crosscorr_iavg[i];
					}
				
					uvputvrd_c(tno,"lst",time_var,1);
					uvwrite_c(tno,preamble,data,flags,npoints);

                } // End of all frames
				// Close output files at end of writing all 16 frame data
				hisclose_c(tno);
				uvclose_c(tno);
		

                } // End of kbhit == 0
		
				frame=0;
				memset(chan1_ind, 0, sizeof(chan1_ind));
				memset(chan2_ind, 0, sizeof(chan2_ind));
				memset(cc_real_ind, 0, sizeof(cc_real_ind));
				memset(cc_img_ind, 0, sizeof(cc_img_ind));
			
				if (kbhit() != 0) /* and if a keyboard hit is detected: exit from loop */
				{
				printf("\n Detected a keyboard hit..stopping..\n");

				// reset switches


				printf("  Counter reset \n");

//				system(command3);
				free(buffer);
				free(stage);
	//			free(chan_data);
	//			close(fa);
				
				printf("  Miriad data written\n");
			
				exit(1);
				}
	  }  // End of code executed if arduino temp is ok....condition check commented at beginning of this loop

	// if the temperature measured by arduino is too high then close and quit....currently commented
	  else  
	  {

//		system(command3);
		free(buffer);
		free(stage);
	//	free(chan_data);
//		close(fa);
		
		printf("Miriad data written..counter reset..quitting because of high temp %f \n", temperature);
		exit(0);
	  }

//	system(command3);        
	free(buffer);
	free(stage);
	//free(chan_data);
//	close(fa);
//	printf("Miriad data written\n");

	return 0;
}

