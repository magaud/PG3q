
// program
// ./t pg33.txt xxx.v 40 130

#include<stdio.h>
#include<stdlib.h>
#define PPL 4

typedef struct { int v4; int p1; int p2; int p3;} s_a3;

void build_principle4(FILE *f, char *name, int n)
{
  int i,j,k,h;
  fprintf(f, "Lemma %s_rect4 : forall P: %s -> %s -> %s -> %s -> Type, \n",
	  name,name,name,name,name);
  for (i=0; i<n; i++)
    for (j=0;j<n;j++)
      for(k=0;k<n;k++)
	for(h=0;h<n;h++)
	  fprintf(f, " P P%d P%d P%d P%d ->\n", i, j,k, h);
  fprintf(f,"forall i j k h:%s,P i j k h.\n",name);
  fprintf(f,"Proof.\n");
  fprintf(f,"idtac \"prove now !\".");
//  fprintf(f, "solve_induction ltac:(%d).\n",n); 
  //fprintf(f, "Optimize Heap. Optimize Proof.\n"); 
  fprintf(f, "Qed.\n");
  fprintf(f, "Check %s_rect.\n\n",name);
}


int belongs(int tab[][PPL], int k, int points_per_line, int v) // checks whether point v belongs to line k
{
  int i,t=1;
  for(i=0;i<points_per_line&&t; i++)
    if (tab[k][i]==v) {t=0;}
  if (t==0) return 1; else return 0;
}

int Pinter(int tab[][PPL], int l1, int l2, int points_per_line, int p, int l)
{
  int i,t=1;
  for(i=0;i<p&&t;i++)
    if (belongs(tab, l1, points_per_line, i)&&(belongs(tab, l2, points_per_line,i))) {break;}
  return i;
}



s_a3 find_v4(int tab[][PPL], int l1, int l2, int l3, int points_per_line, int p, int l)
{
  int t=1,xl;
  s_a3 r;
  for (xl=0;xl<l&&t==1;xl++)
    {
      r.p1=Pinter(tab, xl,l1, PPL, p,l);
      r.p2=Pinter(tab, xl,l2, PPL, p,l);
      r.p3=Pinter(tab, xl,l3, PPL, p,l);
      if ((r.p1!=p)&&(r.p2!=p) && (r.p3!=p))
	{
	  /*printf("xl (%d) = %d %d %d %d\n", xl ,tab[xl][0], tab[xl][1], tab[xl][2], tab[xl][3]);
	    printf("l1 (%d) = %d %d %d %d\n", l1 ,tab[l1][0], tab[l1][1], tab[l1][2], tab[l1][3]);
	    printf("l2 (%d) = %d %d %d %d\n", l2 ,tab[l2][0], tab[l2][1], tab[l2][2], tab[l2][3]);
	    printf("l3 (%d) = %d %d %d %d\n", l3 ,tab[l3][0], tab[l3][1], tab[l3][2], tab[l3][3]);
	    
	    printf("-- P1 = %d, P2 = %d, P3 = %d --\n",p1, p2,p3);
	    //lineP1P2P3(tab, p1,p2,p3, 4, p, l);
	    printf(" -- an appropriate line is %d [ %d %d %d %d]\n\n ", xl,
	    tab[xl][0], tab[xl][1], tab[xl][2], tab[xl][3]);
	    fprintf(f, "(%d,%d,%d) |-> ((o %d %d),((o %d %d), (o %d %d), (o %d %d)))",l1,l2,l3,l,xl,p,p1,p,p2,p,p3);
	    if((l3<l-1)||(l2<l-1)||(l1<l-1)) fprintf(f,",\n"); else fprintf(f,"\n");*/
	  break; //t=0;
	} 
    }
  r.v4=xl;
  /*  if(xl==2) {
    printf("[ -- an appropriate line is %d [ %d %d %d %d]\n", xl, tab[xl][0], tab[xl][1], tab[xl][2], tab[xl][3]);
    printf("Points intersecting are: %d %d %d.]\n",r.p1,r.p2,r.p3);
    }*/
  /*  r.p1=p1;
  r.p2=p2;
  r.p3=p3;*/
  return r;
}

void build_incidence_relation(FILE *f, char *in, int p, int l)
{
  FILE*inp=fopen(in,"r");
  char s[64], tmp[64];
  int (*tab)[PPL] = malloc(sizeof(int[l][PPL]));
  int i=-1, nb_points=PPL,j,k,t,res,l1,l2,l3;
  int compt=-1;
  s_a3 calcul;
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

  // ----------------------- incidence relation
  fprintf(f,"Definition incid_lp (p:Point) (l:Line) (* Point Line *) : bool := \n");
  fprintf(f,"match l with \n");
  for(i=0;i<l;i++)
    {
      fprintf(f, "| L%d => match p with P%d | P%d | P%d => true | _ => false end\n", i,
	      tab[i][0],tab[i][1], tab[i][2]); 
      //      if(i<l-1) fprintf(f,",\n"); else fprintf(f,"\n");
    }
  //fprintf(f,"| _ => false \n");
  fprintf(f,"end.\n\n");

  //  fprintf(f, "Definition incid_lp (p:Point) (l:Line) := incid_N (proj1_sig p) (proj1_sig l).\n\n");
  // -----------------------intersect_lines
  fprintf(f, "Definition f_a2 (l:Line) (m:Line) :=\n");
  fprintf(f, "match l with\n");
  for(i=0;i<l;i++)
    {
      fprintf(f,"| L%d => match m with\n",i);
      for(j=0;j<l;j++)
	{
	  int pi=0,pk,pl;
	  for(pk=0;pk<PPL;pk++)
	    for(pl=0;pl<PPL;pl++)
	      if (tab[i][pk]==tab[j][pl]) {pi=tab[i][pk];}
	  fprintf(f, "| L%d => P%d\n",j,pi);
	}
      fprintf(f,"end\n");
    }
  fprintf(f,"end.\n\n");
  
  
  // ----------------------- l_from_points (a1)
  fprintf(f, "Definition l_from_points (x:Point) (y:Point) : Line :=\n");
  fprintf(f, "match x with\n");
  for (i=0;i<p;i++)
    {fprintf(f, "| P%d =>\n",i);
      fprintf(f, "match y with \n");
    for(j=0;j<p;j++)
      {
	t=1;
	for(k=0;(k<l)&&t;k++)
	  if ((belongs(tab,k, PPL,i))&& belongs(tab,k, PPL,j))
	    {
	      res=k;t=0;
	    }
	fprintf(f, "| P%d => L%d\n", j, res);
      }
    //      fprintf(f,"| _ => L0\n");
      fprintf(f, "end\n");
    }
  //  fprintf(f,"| _ => L0\n");
  fprintf(f, "end.\n\n");
  fprintf(f, "Check l_from_points.\n\n");

  // ----------------------- points_from_line (a3_1)
  fprintf(f, "Definition points_from_line (l:Line) := \n");
  fprintf(f,"match l with \n");

  for(i=0;i<l;i++)
    {
      fprintf(f, "| L%d  =>  (P%d,P%d,P%d) \n",
              i, tab[i][0],tab[i][1], tab[i][2]);
      //if(i<l-1) fprintf(f,",\n"); else fprintf(f,"\n");
    }
  //  fprintf(f, "| _ => (P0,P0,P0,P0)");
  fprintf(f," end.\n\n");
  fprintf(f, "Check points_from_line.\n\n");
  

  fprintf(f, "Definition f_a3_3 (l1:Line) (l2:Line) (l3:Line) := \n");
  fprintf(f, "match l3 with\n");
  //fprintf(f, "  [ fun y:'I_%d => \n",l);
  //fprintf(f, "    [ fun z:'I_%d => (0,(0,0,0)) with \n",l);

  for(l3=0;l3<l;l3++)
    {
      fprintf(f," | L%d => match l2 with \n", l3);
      for(l2=0;l2<=l3;l2++)
	{
	  fprintf(f,"        | L%d => match l1 with \n", l2);
	  for(l1=0;l1<=l2;l1++)
	    {
	       calcul=find_v4(tab,l1,l2,l3, PPL, p,l);
	      
	      fprintf(f,"                  | L%d => (L%d,(P%d,P%d,P%d)) \n", l1, calcul.v4, calcul.p1, calcul.p2, calcul.p3);
	      
	    }
	  if (l1!=l) fprintf(f, "                 | _ => (L0,(P0,P0,P0))\n");
          fprintf(f, "                end\n");
	  //  if (l2<l3) fprintf(f,"x,\n"); else  fprintf(f,"x end\n");
	}
      if (l2!=l) fprintf(f, "       | _ => (L0, (P0,P0,P0))\n");
	fprintf(f, "        end\n");

      //      if (l3<l-1) fprintf(f,"y,\n"); else  fprintf(f,"y\n");
    }

  //fprintf(f, "        | _ => (L0, (P0,P0,P0))\n");
  fprintf(f, "end.\n\n");
  fprintf(f,"Check f_a3_3.\n\n");
  //  fprintf(f, "Eval compute in f_a3_3 (o 130 5) (o 130 8) (o 130 16).\n\n");

  // find a spread
  int m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m;
  int *part = (int *) malloc(sizeof(int[p]));
  int nb=1;
  int somme=0;
  printf("starting computing spreads \n");
  int nb_spreads=0;
  int (*spreads)[10] = malloc(sizeof(int[8500][10])); // approx 8500 spreads in pg(3,3)
  // there are 8424 spreads in pg(3,3)
  for(m1=0;m1<l;m1++)
    {
      //printf("m1=%d\n",m1);
      for(i=0;i<p;i++) part[i]=0;
      //printf("\n");
      part[tab[m1][0]]=1;
      part[tab[m1][1]]=1;
      part[tab[m1][2]]=1;
      part[tab[m1][3]]=1;
      //      for (i=0;i<p;i++) printf("%d", part[i]);
      
      for(m2=m1+1;m2<l;m2++)
	{
	  
	  if((part[tab[m2][0]]==1)
	     || (part[tab[m2][1]]==1)
	     || (part[tab[m2][2]]==1)
	     || (part[tab[m2][3]]==1)) continue;
	  else
	    {
	      part[tab[m2][0]]=1;
	      part[tab[m2][1]]=1;
	      part[tab[m2][2]]=1;
	      part[tab[m2][3]]=1;
	    }
	  
	  for(m3=m2+1;m3<l;m3++)
	    {
	      if((part[tab[m3][0]]==1)
		 || (part[tab[m3][1]]==1)
		 || (part[tab[m3][2]]==1)
		 || (part[tab[m3][3]]==1)) continue;
	      else
		{
		  part[tab[m3][0]]=1;
		  part[tab[m3][1]]=1;
		  part[tab[m3][2]]=1;
		  part[tab[m3][3]]=1;
		}
	      
	      
	      for(m4=m3+1;m4<l;m4++)
		{
		  
		  if((part[tab[m4][0]]==1)
		     || (part[tab[m4][1]]==1)
		     || (part[tab[m4][2]]==1)
		     || (part[tab[m4][3]]==1)) continue;
		  else
		    {
		      part[tab[m4][0]]=1;
		      part[tab[m4][1]]=1;
		      part[tab[m4][2]]=1;
		      part[tab[m4][3]]=1;
		    }
		  for(m5=m4+1;m5<l;m5++)
		    {
		      if((part[tab[m5][0]]==1)
			 || (part[tab[m5][1]]==1)
			 || (part[tab[m5][2]]==1)
			 || (part[tab[m5][3]]==1)) continue;
		      else
			{
			  part[tab[m5][0]]=1;
			  part[tab[m5][1]]=1;
			  part[tab[m5][2]]=1;
			  part[tab[m5][3]]=1;
			}
		      for(m6=m5+1;m6<l;m6++)
			{
			  
			  if((part[tab[m6][0]]==1)
			     || (part[tab[m6][1]]==1)
			     || (part[tab[m6][2]]==1)
			     || (part[tab[m6][3]]==1)) continue;
			  else
			    {
			      part[tab[m6][0]]=1;
			      part[tab[m6][1]]=1;
			      part[tab[m6][2]]=1;
			      part[tab[m6][3]]=1;
			    }
			  for(m7=m6+1;m7<l;m7++)
			    {
			      if((part[tab[m7][0]]==1)
				 || (part[tab[m7][1]]==1)
				 || (part[tab[m7][2]]==1)
				 || (part[tab[m7][3]]==1)) continue;
			      else
				{
				  part[tab[m7][0]]=1;
				  part[tab[m7][1]]=1;
				  part[tab[m7][2]]=1;
				  part[tab[m7][3]]=1;
				}
			      for(m8=m7+1;m8<l;m8++)
				{
				  if((part[tab[m8][0]]==1)
				     || (part[tab[m8][1]]==1)
				     || (part[tab[m8][2]]==1)
				     || (part[tab[m8][3]]==1)) continue;
				  else
				    {
				      part[tab[m8][0]]=1;
				      part[tab[m8][1]]=1;
				      part[tab[m8][2]]=1;
				      part[tab[m8][3]]=1;
				    }
				  for(m9=m8+1;m9<l;m9++)
				    {
				      if((part[tab[m9][0]]==1)
					 || (part[tab[m9][1]]==1)
					 || (part[tab[m9][2]]==1)
					 || (part[tab[m9][3]]==1)) continue;
				      else
					{
					  part[tab[m9][0]]=1;
					  part[tab[m9][1]]=1;
					  part[tab[m9][2]]=1;
					  part[tab[m9][3]]=1;
					}
				      for(m10=m9+1;m10<l;m10++)
					
					{
					  if((part[tab[m10][0]]==1)
					     || (part[tab[m10][1]]==1)
					     || (part[tab[m10][2]]==1)
					     || (part[tab[m10][3]]==1)) continue;
					  else
					    {
					      part[tab[m10][0]]=1;
					      part[tab[m10][1]]=1;
					      part[tab[m10][2]]=1;
					      part[tab[m10][3]]=1;
					    }
					  
					  //printf("all points of these 5 lines %d %d %d %d %d are : ", m1,m2,m3,m4,m5);
					  //					  somme =0;
					  //					  for(i=0;i<p;i++)
					  //if (part[i]) {somme++;}//printf("%d ",i);}
					  //   printf("\n");
					  if(somme==0)//p)
					    {
					      printf("(%d,%d,%d,%d,%d,%d,%d,%d,%d,%d)\n",m1,m2,m3,m4,m5,m6,m7,m8,m9,m10);
					      spreads[nb_spreads][0]=m1;
					      spreads[nb_spreads][1]=m2;
					      spreads[nb_spreads][2]=m3;
					      spreads[nb_spreads][3]=m4;
					      spreads[nb_spreads][4]=m5;
					      spreads[nb_spreads][5]=m6;
					      spreads[nb_spreads][6]=m7;
					      spreads[nb_spreads][7]=m8;
					      spreads[nb_spreads][8]=m9;
					      spreads[nb_spreads][9]=m10;
					      nb_spreads++;
					    }
					  //	      somme=0;
					  part[tab[m10][0]]=0;
					  part[tab[m10][1]]=0;
					  part[tab[m10][2]]=0;
					  part[tab[m10][3]]=0;  
					} // fin m10

				      part[tab[m9][0]]=0;
				      part[tab[m9][1]]=0;
				      part[tab[m9][2]]=0;
				      part[tab[m9][3]]=0;  

				    } // fin m9
				  part[tab[m8][0]]=0;
				  part[tab[m8][1]]=0;
				  part[tab[m8][2]]=0;
				  part[tab[m8][3]]=0;  
				} // fin m8
			      part[tab[m7][0]]=0;
			      part[tab[m7][1]]=0;
			      part[tab[m7][2]]=0;
			      part[tab[m7][3]]=0;  
			    } // fin m7
			  part[tab[m6][0]]=0;
			  part[tab[m6][1]]=0;
			  part[tab[m6][2]]=0;
			  part[tab[m6][3]]=0;  
			} // fin m6
		      part[tab[m5][0]]=0;
		      part[tab[m5][1]]=0;
		      part[tab[m5][2]]=0;
		      part[tab[m5][3]]=0;  
		    } // fin m5
		  part[tab[m4][0]]=0;
		  part[tab[m4][1]]=0;
		  part[tab[m4][2]]=0;
		  part[tab[m4][3]]=0;  
		} // fin m4
	      part[tab[m3][0]]=0;
	      part[tab[m3][1]]=0;
	      part[tab[m3][2]]=0;
	      part[tab[m3][3]]=0;  
	    } // fin m3
	  part[tab[m2][0]]=0;
	  part[tab[m2][1]]=0;
	  part[tab[m2][2]]=0;
	  part[tab[m2][3]]=0;  
	} // fin m2
      part[tab[m1][0]]=0;
      part[tab[m1][1]]=0;
      part[tab[m1][2]]=0;
      part[tab[m1][3]]=0;  
    } // fin m1
  
  printf("nb_spreads = %d\n", nb_spreads);
  // display spreads !
  FILE *g=fopen("spreads_pg33.txt","w");
  for(i=0;i<nb_spreads /*8424*/;i++)
    fprintf(g,"spread #%d : %d %d %d %d %d %d %d %d %d %d\n", i+1,spreads[i][0],spreads[i][1],spreads[i][2],spreads[i][3],spreads[i][4],spreads[i][5],spreads[i][6],spreads[i][7],spreads[i][8],spreads[i][9]);
  fclose(g);

		      
}  


int create_and_write_file(char *in, char *s, int p, int l)
{
  FILE*f=fopen(s,"w");
  int i,j;
  //  fprintf(f, "Add ML Path \"$HOME/math-comp/mathcomp\".\n");
  fprintf(f, "Require Import ssreflect ssrfun ssrbool.\n");
  fprintf(f, "Require Import Generic.lemmas.\n");
  fprintf(f, "Require Import Arith.\n\n");

  fprintf(f, "(* %s: #points = %d, #lines = %d *)\n\n", s, p, l);
  fprintf(f, "Inductive Point :=\n");
  for(i=0;i<p;i++)
    fprintf(f,"| P%d ", i);
  fprintf(f, ".\n\n");

  fprintf(f, "Inductive Line :=\n");
  for(i=0;i<l;i++)
    fprintf(f,"| L%d ", i);
  fprintf(f, ".\n\n");
  
  fprintf(f, "Definition L2nat (l:Line) : nat := match l with \n");
  for(i=0;i<l;i++)
    fprintf(f, "| L%d => %d%%nat\n",i,i);
  fprintf(f,"end.\n\n");

  fprintf(f, "Definition eqL (x y:Line) : bool := Nat.eqb (L2nat x) (L2nat y).\n\n");
  fprintf(f, "Definition leL (x y: Line) : bool := leb (L2nat x) (L2nat y).\n\n");

  fprintf(f, "Lemma leL_total : forall A B, leL A B || leL B A.\n");
  fprintf(f, "Proof.\n");
  fprintf(f, "intros A B; apply Bool.orb_true_iff;\n");
  fprintf(f, "destruct (le_ge_dec (L2nat A) (L2nat B));\n");
  fprintf(f, "  [left; apply leb_correct; assumption |\n");
  fprintf(f, "right; apply leb_correct; unfold ge in *; assumption].\n");
  fprintf(f, "Qed.\n");
  fprintf(f, "\n\n");

  fprintf(f, "Definition P2nat (p:Point) : nat := match p with \n");
  for(i=0;i<p;i++)
    fprintf(f, "| P%d => %d%%nat\n",i,i);
  fprintf(f,"end.\n\n");
  
  fprintf(f, "Definition eqP (x y:Point)  : bool := Nat.eqb (P2nat x) (P2nat y).\n\n");
  fprintf(f, "Definition leP (x y: Point) : bool := leb (P2nat x) (P2nat y).\n");

  fprintf(f, "Lemma leP_total : forall A B, leP A B || leP B A.\n");
  fprintf(f, "Proof.\n");
  fprintf(f, "intros A B; apply Bool.orb_true_iff;\n");
  fprintf(f, "destruct (le_ge_dec (P2nat A) (P2nat B));\n");
  fprintf(f, "  [left; apply leb_correct; assumption |\n");
  fprintf(f, "right; apply leb_correct; unfold ge in *; assumption].\n");
  fprintf(f, "Qed.\n");
  fprintf(f, "\n\n");

  /*fprintf(f, "Definition leP (x y : Point) : bool :=\n");
  fprintf(f, "match x with\n");
  for(i=0;i<p;i++)
    {
      fprintf(f,"| P%d => match y with\n",i);
      for(j=i;j<p;j++)
	fprintf(f, "       | P%d => true \n", j);
      if (i!=0) fprintf(f,"       | _ => false\n"); 
      fprintf(f,"         end\n");
    }

  fprintf(f, "end.\n\n");
  fprintf(f, "Check leP.\n\n");*/
    
  /*fprintf(f, "Definition leL (x y : Line) : bool :=\n");
  fprintf(f, "match x with\n");
  for(i=0;i<l;i++)
    {
      fprintf(f,"| L%d => match y with\n",i);
      for(j=i;j<l;j++)
	fprintf(f, "       | L%d => true \n", j);
      if (i!=0) fprintf(f,"       | _ => false\n"); 
      fprintf(f,"         end\n");
    }

  fprintf(f, "end.\n\n");
   fprintf(f, "Check leL.\n\n");*/
  build_incidence_relation(f, in, p,l);

  //build_principle4(f, "Point", p);
  //fprintf(f, "\n");
  //build_principle(f, "Line", l);
  //fprintf(f, "\n");

  fprintf(f, "(* Local Variables: *)\n");
  fprintf(f, "(* coq-prog-name: \"/Users/magaud/.opam/4.06.0/bin/coqtop\" *)\n");
  fprintf(f, "(* coq-load-path: ((\"/Users/magaud/math-comp/mathcomp\" \"mathcomp\") (\".\" \"Top\")) *)\n");
  fprintf(f, "(* suffixes: .v *)\n");
  fprintf(f, "(* End: *)\n");


  fclose(f);
  return 0; 
}


int main(int argc, char *argv[])
{
  if (argc!=5) {printf("usage: %s  #points #lines input output\n", argv[0]); exit(1);}

  int p = atoi(argv[3]);
  int l = atoi(argv[4]);

  printf("Generating all the required specifications...\n");

  create_and_write_file(argv[1],argv[2], p,l);
  printf("end !\n");
  return 0;
}
