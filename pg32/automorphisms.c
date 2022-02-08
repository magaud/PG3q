// program
// ./a pg32.txt pg32_automorphisms.v 15 35

#include<stdio.h>
#include<stdlib.h>
#include<assert.h>
#define N 1344

#define PPL 3

//typedef struct { int v4; int p1; int p2; int p3;} s_a3;

int belongs(int tab[][PPL], int k, int points_per_line, int v) // checks whether point v belongs to line k
{
  int i,t=1;
  for(i=0;i<points_per_line&&t; i++)
    if (tab[k][i]==v) {t=0;}
  if (t==0) return 1; else return 0;
}

int line(int tab[][PPL], int p1, int p2, int points_per_line, int l)
{
  int i;
  for(i=0;i<l;i++)
    if((belongs(tab, i, PPL,p1)&&belongs(tab, i, PPL,p2)))
      {
	return i;
      }
  return 0; 
}
int third_element(int tab[][PPL], int k, int p1, int p2, int points_per_line, int l)
{
  //printf("The elements of line %d are points %d,%d,%d.\n",k, tab[k][0], tab[k][1], tab[k][2]);
  //printf("The third element of line %d defined by (%d,%d) is %d.\n", k, p1,p2, tab[k][0]+tab[k][1]+tab[k][2]-p1-p2);
  return (tab[k][0]+tab[k][1]+tab[k][2]-p1-p2);
}

int* seven_points_of_plane(int tab[][PPL], int p1, int p2, int p3, int l)
{
  int *plane= (int *)malloc(7*sizeof(int));
  assert(!belongs(tab, line(tab, p1,p2,PPL,l), PPL, p3));
  plane[0]=p1;
  plane[1]=p2;
  plane[2]=third_element(tab,line(tab, p1,p2,PPL,l),p1,p2, PPL,l);
  plane[3]=p3;
  plane[4]=third_element(tab,line(tab, p1,p3,PPL,l),p1,p3, PPL,l);
  plane[5]=third_element(tab,line(tab, plane[2], plane[4],PPL,l),plane[2], plane[4], PPL,l);
  plane[6]=third_element(tab,line(tab, p1, plane[5],PPL,l), p1, plane[5], PPL,l);
  return plane;
}

int in_plane(int tab[][PPL], int x, int p1, int p2, int p3, int l)
{
  int *plane=seven_points_of_plane(tab, p1, p2, p3, l);
  if((x==plane[0])||(x==plane[1])||(x==plane[2])||(x==plane[3])||(x==plane[4])||(x==plane[5])||(x==plane[6]))
    return 1;
  else
    return 0;
}

int Pinter(int tab[][PPL], int l1, int l2, int points_per_line, int p, int l)
{
  int i,t=1;
  for(i=0;i<p&&t;i++)
    if (belongs(tab, l1, points_per_line, i)&&(belongs(tab, l2, points_per_line,i))) {return i;}
  return i;
}

void build_all_automorphisms(FILE *f, char *in, int p, int l)
{
  FILE*inp=fopen(in,"r");
  char s[64], tmp[64];
  int (*tab)[PPL] = malloc(sizeof(int[l][PPL]));
  int i=-1, nb_points=PPL,j,k,m, t,q, res,l1,l2,l3;
  int compt=-1;
  //  s_a3 calcul;
  while(fgets(s,64,inp))
    {
      if(nb_points!=PPL)
	{
	  tab[compt][nb_points]=atoi(s);
	  nb_points++;
	}
      else {nb_points=0;compt++;}
      i++;
    }
  // header for auxiliary file pg32_automorphisms_proofs.v
  FILE*f2;
  f2=fopen("pg32_automorphisms_inv.v","w");

fprintf(f2, "Require Import ssreflect ssrfun ssrbool.\n");
	fprintf(f2, "Require Import Generic.lemmas.\n");
	fprintf(f2, "Require Import PG32.pg32_inductive PG32.pg32_spreads_collineations.\n");
	fprintf(f2, "Require Import PG32.pg32_automorphisms.\n");

	fprintf(f2, "Require Import Lists.List.\n");
	fprintf(f2, "Import ListNotations.\n");
	fprintf(f2, "Require Import Arith.\n\n");
  // end of header
  compt=0;
  for(i=0;i<p;i++)
    for(j=0;j<p;j++)
      for(k=0;k<p;k++)
	for(m=0;m<p;m++)
	{
	  if((i!=j) && (!belongs(tab, line(tab, i, j, PPL, l), PPL, k)) && !in_plane(tab, m, i,j,k,l))
	    {
	      int *plane = seven_points_of_plane(tab, i, j, k, l);
	      int *images = (int *)malloc(p*sizeof(int));
	      images[0]=plane[0];
	      images[1]=plane[1];
	      images[2]=plane[2];
	      images[3]=plane[3];
	      images[4]=plane[4];
	      images[5]=plane[5];
	      images[6]=plane[6];
	      images[7]=m;
	      images[8]=third_element(tab,line(tab,i,m, PPL, l), i,m, PPL, l);
	      images[9]=third_element(tab,line(tab,j,m, PPL, l), j,m, PPL, l);
	      images[10]=third_element(tab,line(tab,plane[2],m, PPL, l), plane[2],m, PPL, l);
	      images[11]=third_element(tab,line(tab,plane[3],m, PPL, l), plane[3],m, PPL, l);
	      images[12]=third_element(tab,line(tab,plane[4],m, PPL, l), plane[4],m, PPL, l);
	      images[13]=third_element(tab,line(tab,plane[5],m, PPL, l), plane[5],m, PPL, l);
	      images[14]=third_element(tab,line(tab,plane[6],m, PPL, l), plane[6],m, PPL, l);
		
	      fprintf(f, "Definition fp_%d (p:Point) :=\n", compt);
	      fprintf(f, " match p with\n");
	      fprintf(f, " | P0 => P%d",images[0]);
	      fprintf(f, " | P1 => P%d",images[1]);
	      fprintf(f, " | P2 => P%d",images[2]);
	      fprintf(f, " | P3 => P%d",images[3]);
	      fprintf(f, " | P4 => P%d",images[4]);
	      fprintf(f, " | P5 => P%d",images[5]);
	      fprintf(f, " | P6 => P%d",images[6]);
	      fprintf(f, " | P7 => P%d",images[7]);
	      fprintf(f, " | P8 => P%d ",images[8]); //third_element(tab,line(tab,i,m, PPL, l), i,m, PPL, l));
	      fprintf(f, " | P9 => P%d ",images[9]); //third_element(tab,line(tab,j,m, PPL, l), j,m, PPL, l));
	      fprintf(f, " | P10 => P%d",images[10]); //third_element(tab,line(tab,plane[2],m, PPL, l), plane[2],m, PPL, l));
	      fprintf(f, " | P11 => P%d",images[11]); //third_element(tab,line(tab,plane[3],m, PPL, l), plane[3],m, PPL, l));
	      fprintf(f, " | P12 => P%d",images[12]); //third_element(tab,line(tab,plane[4],m, PPL, l), plane[4],m, PPL, l));
	      fprintf(f, " | P13 => P%d",images[13]); //third_element(tab,line(tab,plane[5],m, PPL, l), plane[5],m, PPL, l));
	      fprintf(f, " | P14 => P%d\n",images[14]); //third_element(tab,line(tab,plane[6],m, PPL, l), plane[6],m, PPL, l));
	      fprintf(f, " end.\n\n");

	      fprintf(f2, "Definition inv_fp_%d (p:Point) :=\n", compt);
	      fprintf(f2, " match p with\n");

	      for(q=0;q<p;q++)
		fprintf(f2, " | P%d => P%d",images[q],q);
	      fprintf(f2, " end.\n\n");
	      
	      fprintf(f, "Definition fl_%d (p:Line) :=\n", compt);
	      fprintf(f, " match p with\n");
	      for (q=0;q<l;q++)
		fprintf(f, " | L%d => L%d", q, line(tab,images[tab[q][0]], images[tab[q][1]], PPL, l));
	      fprintf(f, " end.\n\n");

	      fprintf(f2, "Definition inv_fl_%d (p:Line) :=\n", compt);
	      fprintf(f2, " match p with\n");
	      for (q=0;q<l;q++)
		fprintf(f2, " | L%d => L%d", line(tab,images[tab[q][0]], images[tab[q][1]], PPL, l), q);
	      fprintf(f2, " end.\n\n");	      
	      free(plane);

	      /*	      fprintf(f, "Lemma collineation_%d : is_collineation fp_%d fl_%d.\n",compt,compt, compt);
	      fprintf(f, "Proof.\n");
	      fprintf(f,"  time (split ;\n");
	      fprintf(f,"    [split;\n");
	      fprintf(f,"    [intros x y; destruct x; destruct y; intros [=]; apply erefl |\n");
	      fprintf(f,"     intros y; exists (inv_fp_%d y); destruct y; apply erefl]\n", compt);
	      fprintf(f,"    | split; [\n");
	      fprintf(f,"        split; \n");
	      fprintf(f, "[ intros x y; destruct x; destruct y; intros [=]; apply erefl\n");
	      fprintf(f, "        | intros y; exists (inv_fl_%d y); destruct y; apply erefl]\n",compt);
	      fprintf(f,"     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).\n");
	      fprintf(f,"Qed.\n\n");
	      fprintf(f,"Check collineation_%d.\n\n",compt);*/
	      
	      compt++;
	    }
	}

  
  int part=-1;
  
  for(i=0;i<compt;i++)
    {
      if(i%(N/14)==0)
	{
	  if (i!=0) { fprintf(f,"].\n\n");}
	  part++;

	  fprintf(f,"Definition all_c%d := [\n",part);
	}
      fprintf(f, "(fp_%d, fl_%d)",i,i);
      if(((i+1)%(N/14))!=0) fprintf(f,"; ");

      //   if(i!=compt-1)     fprintf(f,"; ");
    }
  fprintf(f," ].\n\n");
  
   fprintf(f, "Definition all_collineations := \n");
  for(i=0;i<=part;i++)
    {
      fprintf(f, "all_c%d",i);
      if(i!=part)  fprintf(f," ++ ");
    }
  fprintf(f,".\n\n");
  fprintf(f,"(* %d collineations computed. *)\n\n", compt);
  int indice=0;
  FILE *g;
  for(i=0; i<compt;i++)
    {if(i%N==0)
      {
	indice=i/N;
	char str[30];
	printf("reference name = %s and indice = %d\n",s,indice);
	snprintf(str,30,"pg32_collineations%d.v", indice);
	printf("new file name = %s\n", str);
	//new file
	g=fopen(str,"w");
	fprintf(g, "Require Import ssreflect ssrfun ssrbool.\n");
	fprintf(g, "Require Import Generic.lemmas.\n");
	fprintf(g, "Require Import PG32.pg32_inductive PG32.pg32_spreads_collineations.\n");
	fprintf(g, "Require Import PG32.pg32_automorphisms.\n");
	fprintf(g, "Require Import PG32.pg32_automorphisms_inv.\n");

	fprintf(g, "Require Import Lists.List.\n");
	fprintf(g, "Import ListNotations.\n");
	fprintf(g, "Require Import Arith.\n\n");
	
      }
      
      fprintf(g, "Lemma collineation_%d : is_collineation fp_%d fl_%d.\n",i,i, i);
      fprintf(g, "Proof.\n");
      fprintf(g,"  time (split ;\n");
      fprintf(g,"    [split;\n");
      fprintf(g,"    [intros x y; destruct x; destruct y; intros [=]; apply erefl |\n");
      fprintf(g,"     intros y; exists (inv_fp_%d y); destruct y; apply erefl]\n", i);
      fprintf(g,"    | split; [\n");
      fprintf(g,"        split; \n");
      fprintf(g, "[ intros x y; destruct x; destruct y; intros [=]; apply erefl\n");
      fprintf(g, "        | intros y; exists (inv_fl_%d y); destruct y; apply erefl]\n",i);
      fprintf(g,"     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).\n");
      fprintf(g,"Qed.\n\n");
      fprintf(g,"Check collineation_%d.\n\n",i);
      if((i+1)%N==0)
	{
	  fprintf(g, "Lemma is_col_all_c%d : forall fp fl, In (fp,fl) (all_c%d++all_c%d++all_c%d++all_c%d++all_c%d++all_c%d++all_c%d++all_c%d++all_c%d++all_c%d++all_c%d++all_c%d++all_c%d++all_c%d) -> is_collineation fp fl.\n", indice*14, indice*14, indice*14+1, indice*14+2, indice*14+3,indice*14+4,indice*14+5,indice*14+6,indice*14+7,indice*14+8,indice*14+9,indice*14+10,indice*14+11,indice*14+12,indice*14+13);
	  fprintf(g, "Proof.\n");
	  fprintf(g, " intros fp fl HIn_S.\n");
	  for(q=0;q<N;q++)
	    {
	      fprintf(g, " destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_%d | idtac].\n",indice*N+q);
	    }
	  fprintf(g, " destruct (in_nil HIn_S).\n");
	  fprintf(g, "Qed.\n\n");
	  fclose(g);
	}
    }
  fclose(f2);
  fclose(inp);
}

int create_and_write_file(char *in, char *s, int p, int l)
{
FILE*f=fopen(s,"w");
  int i,j;

  fprintf(f, "Require Import ssreflect ssrfun ssrbool.\n");
  fprintf(f, "Require Import Generic.lemmas.\n");
  fprintf(f, "Require Import PG32.pg32_inductive PG32.pg32_spreads_collineations.\n");

  fprintf(f, "Require Import Lists.List.\n");
  fprintf(f, "Import ListNotations.\n");
  fprintf(f, "Require Import Arith.\n\n");

  //fprintf(f, "Definition fl (fp:Point->Point) := \n");
  //fprintf(f, " fun (l:Line) => l_from_points (fp (fst (fst (points_from_line l)))) (fp (snd (fst (points_from_line l)))).\n\n");

  build_all_automorphisms(f, in, p,l);
  fclose(f);
  return 0; 
}


int main(int argc, char *argv[])
{
  if (argc!=5) {printf("usage: %s input output #points #lines\n", argv[0]); exit(1);}

  int p = atoi(argv[3]);
  int l = atoi(argv[4]);

  printf("Generating the required definitions and computing all automorphisms for PG(3,2)...\n");

  create_and_write_file(argv[1],argv[2], p,l);
  printf("end !\n");
  return 0;
}
