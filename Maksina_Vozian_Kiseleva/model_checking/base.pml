int dv_run=0, acc_run=0, trans_run=0;
int rrr=0;
int sendcom=0;



mtype = {accelon, acceloff, dvigon, dvigoff, reboot, nul, v , vdvig, other};
chan cch = [1] of {mtype};
chan dch = [1] of {mtype};

proctype BIUS(){
mtype command;
mtype c;
mtype dt;
int state=0;
chan poolout = [16] of {mtype};
chan poolin =[16] of {mtype};
int mod=0;

do
  ::
	if
		::(state == 0) && (nfull(poolout)) && (mod!=5) -> {poolout!nul; printf("BIUS: acc off, nul to pool!!!\n");mod=mod+1};
		::(state == 0) && (nempty(poolout)) && (nfull(dch)) -> {poolout?dt; dch!dt; printf("BIUS: acc off, nul to chanel\n")};
		::(state == 0) && (sendcom==2) && (nempty(cch)) && (nfull(poolin))-> {cch ? c; sendcom=0; poolin!c; printf("BIUS: acc off, com to pool\n");mod=0};
		:: (state == 0) && (nempty(poolin))-> {poolin ? command; 
			if
			:: (command==accelon) -> {printf("get accelON\n"); state = 1;acc_run=1};
			:: (command==reboot) -> {printf("get REBOOT\n");
				do
					:: (nempty(poolin)) -> {poolin?command}
					:: (empty(poolin)) -> break
				od;
				do
					:: (nempty(poolout)) -> {poolout?dt}
					:: (empty(poolout)) -> break
				od;mod=0};
			fi};
		::(mod==5) && (empty(poolin)) && (sendcom!=2 || (empty(cch)) || (full(poolin))) && ((empty(poolout)) || (full(dch))) -> {mod=0};
	
		::(state ==1) && (nfull(poolout)) && (mod!=5) -> {poolout!v; printf("BIUS: acc on, v to pool\n");mod=mod+1};
		::(state ==1) && (nempty(poolout)) && (nfull(dch)) -> {poolout?dt; dch!dt; printf("BIUS: acc on, v to chanel\n")};
		::(state ==1) && (sendcom==2) && (nempty(cch)) && (nfull(poolin))-> {cch ? command; sendcom=0; poolin!command; printf("BIUS: acc on, com to pool\n");mod=0};
		::(state ==1) && (nempty(poolin))-> {poolin ? command; 
			if
			:: (command==acceloff) -> {printf("get accelOFF\n"); state = 0}
			fi;mod=0};
		fi
od
}


proctype BKU(){
mtype bkucommand;
mtype bkudt;
int state=0;
chan bkupoolout = [16] of {mtype};
chan bkupoolin =[16] of {mtype};
int time =0;

do
	::(nfull(bkupoolin)) && (nempty(dch)) -> {dch ? bkudt; bkupoolin!bkudt; printf("BKU: get data\n")}
	::(nempty(bkupoolin)) -> {bkupoolin ? bkudt;
		if
			:: (bkudt==nul) ->  printf("BKU: get nul\n")
			:: (bkudt==v) ->  printf("BKU: get v\n")
			:: (bkudt==vdvig) ->  printf("BKU: get vdvig\n")
			:: (bkudt==other) ->  printf("BKU: get other\n")
			
		fi}
	::(state==0) && (len(bkupoolin)>10) && (nfull(bkupoolout))-> { bkupoolout!reboot ; printf("BKU: reboot bius in pool\n");rrr=1}
	::(state==0) && (nempty(bkupoolout)) && (nfull(cch))-> {bkupoolout ? bkucommand; 
		if
			::(bkucommand==reboot) -> {printf("BKU: send reboot\n"); sendcom=2 }
			::(bkucommand==acceloff) -> {printf("BKU: send acceloff\n"); sendcom=2}
			::(bkucommand==dvigoff) -> {printf("BKU: send dvigoff\n"); sendcom=3}
		fi;
		cch!bkucommand}
	
	::(state==0) && (len(bkupoolout)<15)-> { bkupoolout!accelon; bkupoolout!dvigon ; printf("BKU: start trans\n"); state=1; trans_run =1}
	::(state==1) && (nempty(bkupoolout)) && (nfull(cch))-> {bkupoolout ? bkucommand; 
		if
			::(bkucommand==accelon) -> {printf("BKU: send accelon\n"); sendcom=2}
			::(bkucommand==dvigon) -> {printf("BKU: send dvigon\n"); sendcom=3}
		fi;
		cch!bkucommand}
	
	
od
}


proctype DVIG(){
mtype dvcommand;
mtype dvdt;
int state=0;
chan dvpoolout = [16] of {mtype};
chan dvpoolin =[16] of {mtype};
int mod=0;

do
	::(state==0) && (sendcom==3) && (nempty(cch)) && (nfull(dvpoolin))-> {cch ? dvcommand; sendcom=0; dvpoolin!dvcommand; printf("DVIG: dvig off, com to pool\n")}
	::(state ==0) && (nempty(dvpoolin))-> {dvpoolin ? dvcommand; 
		if
		:: (dvcommand==dvigon) -> {printf("DVIG: get dvigON\n"); state = 1; dv_run =1}
		fi}
		
	::(state == 1) && (nfull(dvpoolout)) && (mod!=5) -> {dvpoolout!vdvig; printf("DVIG: dvig on, vdvig to pool\n");mod=mod+1}
	::(state == 1) && (nempty(dvpoolout)) && (nfull(dch)) -> {dvpoolout?dvdt; dch!dvdt; printf("DVIG: dvig on, vdvig to chanel\n")}
		
	::(state==1) && (sendcom==3) && (nempty(cch)) && (nfull(dvpoolin))-> {cch ? dvcommand; sendcom=0; dvpoolin!dvcommand; printf("DVIG: dvig on, com to pool\n");mod=0}
	::(state ==1) && (nempty(dvpoolin))-> {dvpoolin ? dvcommand; 
		if
		:: (dvcommand==dvigoff) -> {printf("DVIG: get dvigOFF\n"); state = 0}
		fi;mod=0}
	::(mod==5) && (state == 1) && ((empty(dvpoolout)) || (nfull(dch))) && ((sendcom!=3) || (empty(cch)) || (full(dvpoolin))) && (empty(dvpoolin))-> {mod=0}

od
}

init
{
run BIUS();
run BKU();
run DVIG();


}


ltl{<>(acc_run==1 && dv_run==1)}
