/*********************** Graphplan **************************************
  (C) Copyright 1995 Avrim Blum and Merrick Furst

  All rights reserved. Use of this software is permitted for non-commercial
  research purposes, and it may be copied only for that use.  All copies must
  include this copyright message.  This software is made available AS IS, and
  neither the authors nor CMU make any warranty about the software or its 
  performance. 
*************************************************************************/

#include <string.h>
#include "graphplan.h"
#include "interface.h"
#include "utilities.h"
#ifndef FALSE
#define FALSE 0
#endif
extern hashtable_t *fact_table, *op_table;  /* the arrays of hash tables */
extern int hash_hits, hash_inserts, hash_numctr, hash_ctr;
extern int do_noexcl;
char templine[100]; /* global var that can use to store lines read in */
extern int do_memo;
fact_list fact_list_from_vertex_list(vertex_t vlist);

/****** newly added ******/
extern char *outputfile;

/***given a string, makes a new one with NOOP in front***
  Returns new storage.
*/
char *make_noop_string(char *str)
{
  char *newp;
  newp = (char *) calloc(strlen(str) + strlen(NOOP) + 2, sizeof(char));
  sprintf(newp,"%s_%s",NOOP,str);
  return newp;
}

/*set uid_mask and uid_block*/
void set_uid(vertex_t v, int id)
{
  v->uid_block = id/32;
  v->uid_mask = 1 << (id % 32);
}


edgelist_t insert_edge(edgelist_t e, vertex_t v)
{
  edgelist_t newedge = (edgelist_t) calloc(1,sizeof(edgelist_s));
  newedge->next = e;
  newedge->endpt = v;
  return newedge;
}

/* like above, but insert at end of list */
edgelist_t insert_edge_at_end(edgelist_t e, vertex_t v)
{
  edgelist_t newedge;
  if (e == NULL) {
    newedge = (edgelist_t) calloc(1,sizeof(edgelist_s));
    newedge->endpt = v;
    return newedge;
  } else {
    e->next = insert_edge_at_end(e->next, v);
    return e;
  }
}

/* like above, but insert at end of list and check for redundency */
/* this function is used in greedy justification procedure */
int insert_vertex_at_end(edgelist_t *e, vertex_t act)
{
  edgelist_t newedge, prevedge, edge;
  
  for (prevedge = edge = *e; edge; prevedge = edge, edge = edge->next) 
    if (act == edge->endpt) /* don't insert action again */
      return 0;
  newedge = (edgelist_t) calloc(1,sizeof(edgelist_s));
  newedge->endpt = act;
  if (*e == NULL) 
    *e = newedge;
  else
    prevedge->next = newedge;
  return 1;
}

void free_edgelist (edgelist_t edge)
{
  edgelist_t e_temp;

  while (edge) {
    e_temp = edge;
    edge = edge->next;
    free(e_temp);
  };
}

/* makes a fact list from the hash table */
fact_list make_list_from_htable(hashtable_t h)
{
  int i;
  fact_list the_facts = NULL,current, p;
  for(i=0; i < HSIZE; ++i)
    if (h[i] != NULL) {
      current = fact_list_from_vertex_list(h[i]);
      for(p = current;  p->next; p = p->next);
      p->next = the_facts;
      the_facts = current;
    }
  return( the_facts );
}

void completely_free_fact_list(fact_list l)
{
  char *s;
  fact_list temp;
  while(l) { 
    temp = l->next;
    if (l->item) {
      s = l->item->item;
      if ((strcmp(s, "exists") == 0) || (strcmp(s, "forall") == 0))
	completely_free_fact_list(l->body);
      free_token_list(l->item);
    }
    free(l); 
    l = temp;
  }
}

void free_token_list(token_list l)
{
  token_list temp;
  while(l) {   temp = l->next; free(l->item); free(l); l = temp;  }
}


/* makes string list into fact list. */
fact_list fact_list_from_vertex_list(vertex_t vlist)
{
  fact_list retval = NULL, f;
  char *str;
  for(; vlist; vlist = vlist->next) {
    str = vlist->name;
    f = (fact_list) malloc(sizeof(fact_list_elt));
    f->next = retval;
    retval = f;
    f->item = token_list_from_string(str);
  }
  return retval;
}

token_list token_list_from_string(char str[])
{
  char *p = str, *q, temp[50];
  token_list_elt dummy, *current;
  current = &dummy;
  while (*p) {
    current->next = (token_list) malloc(sizeof(token_list_elt));
    current = current->next;
    for(q = temp; (*p != '\0') && (*p != CONNECTOR); *q++ = *p++);
    if (*p == CONNECTOR) ++p;
    *q = '\0';
    current->item = (char *) calloc(1 + strlen(temp),sizeof(char));
    strcpy(current->item, temp);
  }
  current->next = NULL;
  return( dummy.next );
}


/* insert into instantiation list */
instantiation_list insert_inst(char *v, char *c, instantiation_list i)
{
  instantiation_list temp=(instantiation_list) malloc(sizeof(instantiation_s));
  temp->var_part = v;
  temp->const_part = c;
  temp->next = i;
  return( temp );
}


/* Returns instantiate token list in a string (last argument) Uses
   CONNECTOR to connect the tokens together. 
   if "failflag" is 0 then Return 1 if ok, 0 if failure.
   Otherwise, exit on failure.
   */
int instantiate_into_string(token_list l, instantiation_list inst,char str[],
			    int failflag)
{
  instantiation_list i;
  char *p;
  token_list t = l;

  for(p = str; t; t = t->next) {
    if (is_const(t->item))  /* just copy over */
      { strcpy(p,t->item); p+=strlen(t->item); *p++ = CONNECTOR; }
    else {
      for(i=inst; i; i = i->next)
        if (strcmp(i->var_part, t->item) == SAME) {
	  if (i->const_part == NULL) {i = NULL; break;}
          strcpy(p,i->const_part);p+=strlen(i->const_part);*p++ = CONNECTOR;
          break;
        }
      if (!i) {
	if (failflag) do_error("instantiation failed");
	return 0;
      }
    }
  }
  *(--p) = '\0';
  return 1;
}

/* "whitespace" is blank or paren */
int is_stopper(int c)
{
  return (isspace(c) || (c == ')') || (c == '('));
}

/* read the next "item".  An item is either a string of non-parentesis,
   non-blank characters, or a parenthesis.  In the former case, put into
   str and return OK. In the latter case, return LEFT_PAREN or RIGHT_PAREN
   appropriately.  Return EOF on end-of-file.

   if character is CONNECTOR, change it to REPLACEMENT
 */
/*
#define REPLACEMENT '.'
int read_item(FILE *fp, char *str)
{
  char *s = str;
  int letter, var_flag;
  // first read in any blankspace and check for EOF 
  while(isspace(letter = getc(fp)));
  if (letter == EOF) return EOF;

  // check if parenthesis 
  if (letter == '(') return LEFT_PAREN;
  if (letter == ')') return RIGHT_PAREN;
  //  if (letter == ':') return SEMI_COLON; 
  ifmake
 (letter == ';') {
    while (getc(fp) != '\n');
    return read_item(fp, str);
  }
  var_flag = 0;
  if (letter == '?') {
    var_flag = 1;
    letter = '<';
  }
  ungetc((char) letter, fp);
while(!is_stopper(*s++ = tolower(getc(fp))))    // read word in 
     if (*(s-1) == CONNECTOR) *(s-1) = REPLACEMENT;  // change '_'to'.'
    ungetc(*--s, fp);                      //went one too far 
  if (var_flag)
    *s++ = '>';
    *s = '\0';                           // end it nicely 
    if (strcmp(str, "not") == 0) {	 // "not" -> "del" 
    strcpy(str, "del");
  }
if (strcmp(str, "and") == 0) {	 	// handle "and" 
    return CAND;
  }
  return OK;
}
*/
/* string to describe an instantiated operator: re-reverse order */
void rec_make_op_string(op_ptr op,instantiation_list insts, char *str)
{
  if (insts == NULL) return;
  rec_make_op_string(op, insts->next, str);
  if (insts->const_part == NULL) 
    {fprintf(STDMSG,"op %s, ",op->name); do_error("bad instantiation");}
  sprintf(str + strlen(str), "_%s", insts->const_part);
}
/* string to describe an instantiated operator */
void make_op_string(op_ptr op, char *str)
{
  sprintf(str, "%s",op->name);
  rec_make_op_string(op, op->insts, str + strlen(str));
}

void do_error(char *s)
{
  fprintf(STDMSG,"%s\n",s); exit( 1 );
}

int equal_facts(token_list f1, token_list f2)
{
  for(; f1 && f2; f1 = f1->next, f2 = f2->next)
    if (!equal_tokens(f1->item,f2->item)) return 0;  /* different tokens*/
  if (f1 || f2) return 0;  /* different lengths */
  return 1;
}


/************ ROUTINES FOR DOING MUTUAL EXCLUSION RELATIONS ************
 ************ --SHOULD PROBABLY BE IN A DIFFERENT FILE      ************/

/* Note: the first fact layer doesn't have uids set, but then again, they
   aren't exlusive either */
int are_mutex(vertex_t v1, vertex_t v2)
{
  return ((v1->exclusive_vect[v2->uid_block]) & (v2->uid_mask));
}

int are_mutex_in_this_step(vertex_t v1, vertex_t v2)
{
  return ((v1->excl_in_this_step_vect[v2->uid_block]) & (v2->uid_mask));
}


/* Given time in op hash table, finds all mutually exclusive ops.
 */
void find_all_mutex_ops(hashtable_t harr[], int time)
{
  vertex_t v;
  get_next(harr[time],0); /* initialize */
  while((v = get_next(harr[time],1)) != NULL)
    find_mutex_ops(v, time);
  return;
}

/* make exclusive if they aren't already */
void do_exclusive(vertex_t v, vertex_t v2)
{
  if (are_mutex(v,v2)) return;
  v->exclusive_vect[v2->uid_block] |= v2->uid_mask;
  v2->exclusive_vect[v->uid_block] |= v->uid_mask;
  v->exclusive = insert_edge(v->exclusive, v2);
  v2->exclusive = insert_edge(v2->exclusive, v);
}
	

/* Given a vertex representing an operator, it finds other mutually-exclusive
 * ops. 
 *
 * The method is: (1) if a precond p is mutually exclusive with another fact 
 * q s.t. q is a precond for another op then the ops are also mutually 
 * exclusive. 
 *
 * LOCAL PART: If the operator deletes something that is either 
 * someone else's precondition or someone else's effect, then the two ops 
 * are exclusive.  THE REASON FOR THIS is (I) if you delete a precond then 
 * impossible to do both, and (II) if you delete an effect, then the order of 
 * these ops will matter, though this only is a problem in domains where an op
 * might add a fact that was already there (otherwise these two can't possibly 
 * happen at the same time anyway).
 *
 * NEW: Make noop exclusive of any other action which adds its effect. The
 * Reason is that you need never include both in a plan.
 *
 * ALSO: put into del_edges.
 *
 * For speedup: for type(1) only call do_exclusive for vertices v2 
 * for which v<v2 as ptrs
 */
void find_mutex_ops(vertex_t v, int time)
{
  string_list slist;
  edgelist_t temp1, temp2, temp3;
  vertex_t v2, nextfact, prevfact;

  /* Do type (1) */
  for(temp1 = v->in_edges; temp1; temp1 = temp1->next) {
    for(temp2 = temp1->endpt->exclusive; temp2; temp2 = temp2->next) {
      for(temp3 = temp2->endpt->out_edges; temp3; temp3 = temp3->next) {
	v2 = temp3->endpt;  /* this is the op to check */
	if ((int) v < (int) v2) do_exclusive(v, v2);    /* Do it */
      }
    }
  }
  
  /* LOCAL PART: */
  for(slist = v->del_list; slist; slist = slist->next) {
    nextfact = lookup_from_table(fact_table[time+1], slist->item);
    if (nextfact == NULL) {
      if (DEBUG_FLAG > 1) fprintf(STDMSG,"%s deleting nonexistent fact\n",v->name);
      continue;
    }
    prevfact = nextfact->prev_time;
    /* do preconditions */
    if (prevfact) {
      for(temp2 = prevfact->out_edges; temp2; temp2 = temp2->next) {
	if (v != temp2->endpt) {
	  do_exclusive(v, temp2->endpt);
	}
      }
    }
    /* now effects */
    for(temp2 = nextfact->in_edges; temp2; temp2 = temp2->next) {
      if (v != temp2->endpt) {
	do_exclusive(v, temp2->endpt);
      }
    }
    /* now put into del_edges (and put info into FACT too, for DELETES)*/
    v->del_edges = insert_edge(v->del_edges, nextfact);
    nextfact->del_edges = insert_edge(nextfact->del_edges,v);
  }
  /* free storage of delete list */
  while(v->del_list) {
    slist = v->del_list;
    v->del_list = v->del_list->next;
    free(slist);
  }
  /* SPECIAL for NOOPs */
  if (v->is_noop) {
    for(temp2 = v->out_edges->endpt->in_edges; temp2; temp2 = temp2->next) {
      if (v != temp2->endpt) 
	do_exclusive(v, temp2->endpt);
    }
  }
}

/* Given two vertices representing facts, are they mutually exclusive?
 * just see if all ops generating p are exclusive of all ops generating q.
 */
int are_facts_exclusive(vertex_t p, vertex_t q)
{
  edgelist_t temp1, temp2;
  if (do_noexcl) return 0; /* option to turn off exclusivity */
  for(temp1 = p->in_edges; temp1; temp1 = temp1->next) {
    for(temp2 = q->in_edges; temp2; temp2 = temp2->next) {
      if (!are_mutex(temp1->endpt, temp2->endpt)) return 0;
    }
  }
  if (DEBUG_FLAG>2) fprintf(STDMSG, "Facts %s and %s mutually exclusive\n",
			   p->name, q->name);
  return 1;
}



/* Given time in fact hash table, finds all mutually exclusive facts.
 * Assumes there are no more than MAXNODES facts at this time step.
 * Returns number of facts and number of exclusive pairs.
 *
 * Note: varr is used in find_currently_mutex_facts too.
 *
 */
static vertex_t *varr;
bbpair find_mutex_facts(hashtable_t harr[], int time)
{
  static int flag = 0;
  bbpair retval;
  edgelist_t e;
  vertex_t v;
  int i, j, fcount=0, ecount=0;
  if (flag == 0) {  /* doing this since MAXNODES is not a constant */
    varr = (vertex_t *) malloc(MAXNODES*sizeof(vertex_t));
    flag = 1;
  }
  get_next(harr[time],0); /* initialize */
  for(i=0; (varr[i] = get_next(harr[time],1)) != NULL; ++i);
  for(i=0; varr[i] != NULL; ++i) {
    ++fcount;
    /* if it's NEW, then check against everybody */
    if (!varr[i]->prev_time) {
      for(j=0; varr[j] != NULL; ++j) {
	if (!varr[j]->prev_time && j <= i) continue; /* already checked */
	if (are_facts_exclusive(varr[i], varr[j])) {
	  ++ecount;
	  do_exclusive(varr[i], varr[j]);
	}
      }
    } else { /* OLD, so only check previous exclusives */
      for(e = varr[i]->prev_time->exclusive; e; e = e->next) {
	v = e->endpt->next_time;
	if ((int) v < (int) varr[i]) continue;  /* get in other direction */
	if (are_facts_exclusive(varr[i], v)) {
	  ++ecount;
	  do_exclusive(varr[i], v);
	}
      }
    }
  }
  retval.first = fcount;
  retval.second = ecount;
  return retval;
}

/* This routine looks at a pairs of facts at a given time step such that 
   neither fact is in the initial state, and returns 1 if they cannot both 
   be created by ops in this time step.

   Note: be sure to skip over the noops here.  
*/
int are_facts_excl_in_this_step(vertex_t v1, vertex_t v2)
{
  edgelist_t e1, e2;
  for(e1 = v1->in_edges; e1; e1 = e1->next) {
    if (IS_NOOP(e1->endpt)) continue;
    for(e2 = v2->in_edges; e2; e2 = e2->next) {
      if (IS_NOOP(e2->endpt)) continue;
      if (!are_mutex(e1->endpt, e2->endpt)) return 0;
    }
  }
  return 1;
}

/* make them excl in this step */
void do_excl_in_this_step(vertex_t v1, vertex_t v2)
{
  v1->excl_in_this_step_vect[v2->uid_block] |= v2->uid_mask;
  v2->excl_in_this_step_vect[v1->uid_block] |= v1->uid_mask;
  v1->excl_in_this_step = insert_edge(v1->excl_in_this_step, v2);
  v2->excl_in_this_step = insert_edge(v2->excl_in_this_step, v1);
}
	
/* This routine looks at all pairs of facts a given time step and for each
   pair such that neither fact is in the initial state marks the two facts as
   "excl_in_this_step" if they cannot both be created by ops in this time step.

   Using same storage as find_mutex_facts, so CALL THIS ONE AFTER
   CALLING find_mutex_facts.
 */
void find_currently_mutex_facts()
{
  edgelist_t e;
  vertex_t v2;
  int i, j;
    
  /* initialization of varr done already in find_mutex_facts */

  for(i=0; varr[i] != NULL; ++i) {
    if (lookup_from_table(fact_table[0],varr[i]->name)) continue;

    /* if it's NEW, then check against everybody */
    if (!varr[i]->prev_time) {
      for(j=0; varr[j] != NULL; ++j) {
	if (!varr[j]->prev_time && j <= i) continue; /* already checked */
	if (lookup_from_table(fact_table[0],varr[j]->name)) continue;
	if (are_facts_excl_in_this_step(varr[i], varr[j]))
	  do_excl_in_this_step(varr[i], varr[j]);
      }
    } else {               /* OLD, so only check previous exclusives */
      for(e = varr[i]->prev_time->excl_in_this_step; e; e = e->next) {
	v2 = e->endpt->next_time;
	if ((int) v2 < (int) varr[i]) continue;  /* get in other direction */
	if (are_facts_excl_in_this_step(varr[i], v2))
	  do_excl_in_this_step(varr[i], v2);
      }
    }
  }
}
/*************************END MUTUAL EXCLUSION PART**********************/





/************ ROUTINES FOR PRINTING OUT INFORMATION TO USER**************/
void print_info_piece(hashtable_t t, int flag)
{
  vertex_t vert;
  edgelist_t edge;
  get_next(t, 0); /* get ready */
  while((vert = get_next(t, 1)) != NULL) {
    if (vert->needed == 0 || IS_NOOP(vert)) continue;
    fprintf(STDMSG, "%s\n",vert->name);
    if (flag>=2 && ((edge = vert->exclusive) != NULL)) {
      fprintf(STDMSG, "   exclusive: "); /* now, includes noops */
      for(; edge; edge = edge->next)
	if (edge->endpt->needed) fprintf(STDMSG, "%s ",edge->endpt->name);
      fprintf(STDMSG, "\n");
    }
  }
}

/* for printing out info to user */
void print_info(int len)
{
  int i;
fprintf(STDMSG, "Printing graph. For clarity, ignoring parts unreachable by planner\n");
  remove_unneeded_vertices(len);  /**just for printing **/

  for(i=0; i < len; ++i) {
    fprintf(STDMSG, "\nTime: %d\n",i+1);
    print_info_piece(op_table[i], DEBUG_FLAG);
    if (DEBUG_FLAG >= 2) {
      fprintf(STDMSG, "\nFacts: \n");
      print_info_piece(fact_table[i+1], 2); /* PRINT FACTS*/
    }
  }
}


/************ more random utilities ***************/
void read_initial_comments(FILE *fp)
{
  int c;
  while((c = getc(fp)) != '(');  /* read up to first left paren */
}

int allocs_in_use;

void my_free(void * p) {
    allocs_in_use--;
    free(p);
}
void * my_alloc(int size) {
    void * p = malloc(size);
    allocs_in_use++;
    if (p == NULL) {
        fprintf(STDMSG, "Ran out of space.  Requested size=%d.\n", size);
        exit(1);
    }
    return p;
}

void print_alloc(void)
{ fprintf(STDMSG, "allocs - frees = %d\n",allocs_in_use); }

/*
void yyerror(char *x)
{
	fprintf(STDMSG, "%s\n",x);
}
*/

fact_list fact_list_append(fact_list f1, fact_list f2)
{
  fact_list f;
  
  if (f1 == NULL) return f2;
  for (f = f1; f->next; f = f->next);
  f->next = f2;
  return f1;
}


token_list token_list_append(token_list f1, token_list f2)
{
	if (f2 == NULL) return f1;

	if (f1 == NULL) return f2;

	f1->next = token_list_append(f1->next, f2);

	return f1;
}

/* simply printout no plan if necessary */
void print_nosolution (void)
{
  FILE *outputfp;
  
  if (outputfile) {
    if ((outputfp = fopen(outputfile,"a")) == NULL) 
      do_error("cannot open output file");
    fprintf(outputfp, "NO SOLUTION\n");
    fclose(outputfp);
  }
}

void no_solution(char * msg, int time)
{
    fprintf(STDMSG, "\n----------------------------------------------------\n");    
    fprintf(STDMSG, "NO SOLUTION\n");
    fprintf(STDMSG, "Problem not solvable: %s\n", msg);
    fprintf(STDMSG, "    Search halted after %d steps\n", time);
    if (do_memo) { 
	fprintf(STDMSG, "    %d entries in hash table and %d hits\n",hash_inserts, hash_hits);
	fprintf(STDMSG, "    avg set size %d\n", hash_numctr/( hash_ctr ? hash_ctr : 1));
    }
    fprintf(STDMSG, "----------------------------------------------------\n");
    print_nosolution();
}

/*********************************************
 * routines added for blackbox 
 *********************************************/

void 
free_fact_list (fact_list l)
{
  fact_list temp;
  while(l) { 
    temp = l->next; 
    free_fact_list(l->body);
    free_token_list(l->item); 
    free(l); 
    l = temp;}
}


/* lookup the constant part in the instantiation */
char* lookup_instantiation (instantiation_list insts, char *name)
{
  for (; insts; insts = insts->next) {
    if (strcmp(insts->var_part, name) == 0)
      return insts->const_part;
  }
  return NULL;
}

/* free instantiation list; assume var_part & const_part are shared */
void free_instantiation (instantiation_list insts)
{
  instantiation_list temp;

  while(insts) {
    temp = insts->next;
    free(insts);
    insts = temp;
  }
}

/* make a fact from a token */
fact_list token2fact (token_list tlist)
{
  fact_list f;
  f = (fact_list) calloc(1, sizeof(fact_list_elt));
  f->item = tlist;
  // f->next = NULL;
  return f;
}

/* make a token from a string */
token_list str2token (char *str)
{
  token_list tlist;
  
  tlist = (token_list)calloc(1, sizeof(token_list_elt));
  tlist->item = str;
  // tlist->next = NULL;
  return tlist;
}

/* duplicate a string and from a token */
token_list strdup2token (char *str)
{
  token_list tlist;
  
  tlist = (token_list)calloc(1, sizeof(token_list_elt));
  tlist->item = bbstrdup(str);
  // tlist->next = NULL;
  return tlist;
}

/* duplicate a token list */
token_list dup_token_list (token_list tlist)
{
  token_list thead, tcur, tnew;
  
  thead = tcur = NULL;
  while (tlist != NULL) {
    tnew = strdup2token(tlist->item);
    if (thead == NULL)
      thead = tcur= tnew;
    else {
      tcur->next = tnew;
      tcur = tnew;
    }
    tlist = tlist->next;
  }
  return thead;
}

/* duplicate a fact list */
fact_list dup_fact_list (fact_list flist)
{
  fact_list fhead, fcur, fnew;

  fhead = fcur = 0;
  for (; flist; flist = flist->next) {
    fnew = token2fact(dup_token_list(flist->item));
    if (fhead == 0)
      fhead = fcur = fnew;
    else {
      fcur->next = fnew;
      fcur = fnew;
    }
  }
  return fhead;
}

/* print token list */
void print_token_list (FILE *fp, token_list t)
{
  int flag = 0;
  fprintf (fp, "(");
  while (t != NULL) {
    if (flag)
      fputc(' ', fp);
    else
      flag = 1;
    fprintf (fp, "%s", t->item);
   t = t->next; 
  }
  fputc (')', fp);
}

/* print fact list */
void print_fact_list (fact_list f)
{
  while (f != NULL) {
    print_token_list(STDMSG, f->item);
    f = f->next;
  }
  fprintf (STDMSG, "\n");
}

/* print acitons for debugging */
void print_actions (op_list op)
{
  while (op != NULL) {
    fprintf (STDMSG, "action %s:\n", op->name);
    fprintf (STDMSG, "parameters => ");
    print_fact_list (op->params);
    fprintf (STDMSG, "precondsions => ");
    print_fact_list (op->preconds);
    fprintf (STDMSG,"effects => ");
    print_fact_list (op->effects);
    fprintf (STDMSG, "\n");
    op = op->next;
  }
}

/* same as strdup, except all characters are converted to lower case */
char* bbstrdup (char* s1)
{
  char *str, *p;  

  str = (p = strdup(s1));
  while (*p) {
    if (*p == CONNECTOR)
      *p = '-';
    *p = tolower(*p);
    p++;
  }
  return str;
}

/* find a token in a fact list */
/* return 1: str in the token list, 0: str is not in the token list */
fact_list find_fact_list (fact_list fact, token_list token)
{
  for (; fact; fact = fact->next) {
    if (equal_facts(fact->item, token))
      return fact;
  }
  return NULL;
}


/* Luby's series */
long luby_super(int i)
{
    long power;
    int k;

    if (i<=0){
        fprintf(stderr, "bad argument super(%d)\n", i);
        exit(1);
    }
    /* let 2^k be the least power of 2 >= (i+1) */
    k = 1;
    power = 2;
    while (power < (i+1)){
        k += 1;
        power *= 2;
    }
    if (power == (i+1)) return (power/2);
    return (luby_super(i - (power/2) + 1));
}

void
print_instantiation (instantiation_list list)
{
  for (; list; list = list->next) {
    printf("var = %s const = %s\n", list->var_part, list->const_part);
  }
  printf("---------------\n");
}
