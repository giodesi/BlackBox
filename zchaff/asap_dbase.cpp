/* =========FOR INTERNAL USE ONLY. NO DISTRIBUTION PLEASE ========== */

/*********************************************************************
 Copyright 2000-2001, Princeton University.  All rights reserved. 
 By using this software the USER indicates that he or she has read, 
 understood and will comply with the following:

 --- Princeton University hereby grants USER nonexclusive permission 
 to use, copy and/or modify this software for internal, noncommercial,
 research purposes only. Any distribution, including commercial sale 
 or license, of this software, copies of the software, its associated 
 documentation and/or modifications of either is strictly prohibited 
 without the prior consent of Princeton University.  Title to copyright
 to this software and its associated documentation shall at all times 
 remain with Princeton University.  Appropriate copyright notice shall 
 be placed on all software copies, and a complete copy of this notice 
 shall be included in all copies of the associated documentation.  
 No right is  granted to use in advertising, publicity or otherwise 
 any trademark,  service mark, or the name of Princeton University. 


 --- This software and any associated documentation is provided "as is" 

 PRINCETON UNIVERSITY MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS 
 OR IMPLIED, INCLUDING THOSE OF MERCHANTABILITY OR FITNESS FOR A 
 PARTICULAR PURPOSE, OR THAT  USE OF THE SOFTWARE, MODIFICATIONS, OR 
 ASSOCIATED DOCUMENTATION WILL NOT INFRINGE ANY PATENTS, COPYRIGHTS, 
 TRADEMARKS OR OTHER INTELLECTUAL PROPERTY RIGHTS OF A THIRD PARTY.  

 Princeton University shall not be liable under any circumstances for 
 any direct, indirect, special, incidental, or consequential damages 
 with respect to any claim by USER or any third party on account of 
 or arising from the use, or inability to use, this software or its 
 associated documentation, even if Princeton University has been advised
 of the possibility of those damages.
*********************************************************************/

#include "asap_dbase.h"

CDatabase::CDatabase()  { 
    _stats.mem_used_up_counts = 0;
    _stats.mem_used_up = false;

    _stats.init_num_clauses = 0;
    _stats.init_num_literals = 0;
    _stats.num_added_clauses = 0;
    _stats.num_added_literals = 0;
    _stats.num_deleted_clauses = 0;
    _stats.num_deleted_literals = 0;

    _lit_pool_start = new CLitPoolElement[STARTUP_LIT_POOL_SIZE]; 
    _lit_pool_finish = _lit_pool_start;
    _lit_pool_end_storage = _lit_pool_start + STARTUP_LIT_POOL_SIZE;
    lit_pool_push_back(0); //set the first element as a spacing element

    _mem_limit = 1024*1024*512; //that's 0.5 G
}


void CDatabase::compact_lit_pool(void)
{
    int i;
    
    CHECK(cout << "Begin Compaction " << endl;);
    int new_index = 1;
    for (i=1; i< lit_pool_size(); ++i){ //begin with 1 because 0 position is always 0
	if (lit_pool(i).val()<=0 && lit_pool(i-1).val()<=0)
	    continue;
	else {
	    lit_pool(new_index) = lit_pool(i);
	    ++new_index;
	}
    }
    _lit_pool_finish = lit_pool_begin() + new_index;
    //update all the pointers of the clauses;
    //1. clean up the pt pointers from variables
    for (i=1; i<variables().size(); ++i) {
	variable(i).ht_ptr(0).clear();
	variable(i).ht_ptr(1).clear();
    }
    //2. reinsert the ht_pointers
    for (i=1; i< lit_pool_size(); ++i) {
	if (lit_pool(i).val() > 0 && lit_pool(i).is_ht()) {
	    int var_idx = lit_pool(i).var_index();
	    int sign = lit_pool(i).var_sign();
	    variable(var_idx).ht_ptr(sign).push_back(& lit_pool(i));
	}
    }
    //3. update the clauses' first literal pointer
    for (i=1; i< lit_pool_size(); ++i) {
	if (lit_pool(i).val() <= 0) {
	    int cls_idx = -lit_pool(i).val();
	    clause(cls_idx).first_lit() = &lit_pool(i) - clause(cls_idx).num_lits();
	}
    }
    CHECK(output_lit_pool_state(); 
	  cout << endl << endl;);
}

bool CDatabase::enlarge_lit_pool(void) //will return true if successful, otherwise false.
{
    int i;
    
    CHECK (output_lit_pool_state());
    if (lit_pool_size() - num_clauses() > num_literals() * 2) {
	//memory fragmented. ratio of efficiency < 0.5
	//minus num_clauses() is because of spacing for 
	//each clause in lit_pool
	compact_lit_pool();
	return true;
    }
    CHECK(cout << "Begin Enlarge Lit Pool" << endl;);

    //otherwise we have to enlarge it.
    //first, check if memory is running out
    int current_mem = estimate_mem_usage();
    float grow_ratio;
    if (current_mem < _mem_limit /2 ) {
	grow_ratio = 2;
    }
    else if (current_mem < _mem_limit * 0.8) {
	grow_ratio = 1.2;
    }
    else {
	_stats.mem_used_up = true;
	if (lit_pool_size() - num_clauses() > num_literals() * 1.1) {
	    compact_lit_pool();
	    return true;
	}
	else 
	    return false;
    }
    //second, make room for new lit pool.
    CLitPoolElement * old_start = _lit_pool_start;
    CLitPoolElement * old_finish = _lit_pool_finish;
    int old_size = _lit_pool_end_storage - _lit_pool_start;
    int new_size = (int)(old_size * grow_ratio);
    _lit_pool_start = new CLitPoolElement[new_size];
    _lit_pool_finish = _lit_pool_start;
    _lit_pool_end_storage = _lit_pool_start + new_size;
    //copy the old content into new place
    for (CLitPoolElement * ptr = old_start; ptr != old_finish; ++ptr) {
	*_lit_pool_finish = *ptr;
	_lit_pool_finish ++;
    }
    //update all the pointers
    int displacement = _lit_pool_start - old_start;
    for (i=0; i< clauses().size(); ++i)
	if (clause(i).in_use()) 
	    clause(i).first_lit() += displacement; 

    for (i=0; i< variables().size(); ++i) {
	CVariable & v = variable(i);
	for (int j=0; j< 2 ; ++j) {
	    vector<CLitPoolElement *> & ht_ptr = v.ht_ptr(j);
	    for (int k=0; k< ht_ptr.size(); ++k) {
		ht_ptr[k] += displacement; 
	    }
	}
    }
    //free old space
    delete [] old_start;
    CHECK(output_lit_pool_state());
    CHECK(cout << endl << endl);
    return true;
}

ClauseIdx CDatabase::add_clause(int * lits, int n_lits) { 
    int new_cl;
    //a. do we need to enlarge lits pool?
    while (lit_pool_free_space() <= n_lits + 1) { 
	if (enlarge_lit_pool()==false) 
	    return -1; //mem out, can't enlarge lit pool, because 
	               //ClauseIdx can't be -1, so it shows error.
    }	
    //b. get a free cl index;
    if (_unused_clause_idx_queue.empty()) {
	new_cl = _clauses.size();
	_clauses.resize(new_cl + 1);
    }
    else {
	new_cl = _unused_clause_idx_queue.front();
	_unused_clause_idx_queue.pop();
    }
    //c. add the clause lits to lits pool
    clause(new_cl).init(lit_pool_end(), n_lits);

    //I want to verify added clauses are either all free or all 0
    bool all_free_lits = true, all_zero_lits = true;
    for (int i=0; i< n_lits; ++i){
	int var_idx = lits[i]>>1;
	assert(var_idx < variables().size());
	int var_sign = lits[i]&0x1;
	lit_pool_push_back( ((var_idx<<1) + var_sign) << 2);
	++variable(var_idx).lits_count(var_sign);
	int lit_value = literal_value(clause(new_cl).literal(i));

	if (lit_value != 0)
	    all_zero_lits = false;
	if (lit_value == 0 || lit_value == 1) //e.g. not unknown
	    all_free_lits = false;
    }
    assert(all_zero_lits || all_free_lits);
    lit_pool_push_back(-new_cl); //push in the clause idx in the end
    //d. set the head/tail pointers
    if (clause(new_cl).num_lits() > 1) {
	//add the ht. note: ht must be the last free var
	int max_idx = -1, max_dl = -1;
	CClause & cl = clause(new_cl);
	int i, sz = cl.num_lits();
	int other_ht_idx;
	CVariable * my_var;
	for (i=0; i< sz; ++i) {
	    int v_idx = cl.literals()[i].var_index();
	    my_var = &variable(v_idx);
	    if (variable(v_idx).value()==UNKNOWN) {
		int v_sign = cl.literals()[i].var_sign();
		variable(v_idx).ht_ptr(v_sign).push_back( & cl.literals()[i]);
		cl.literals()[i].set_ht(1);
		other_ht_idx = i;
		break;
	    }
	    else {
		if (variable(v_idx).dlevel() > max_dl) {
		    max_dl = variable(v_idx).dlevel();
		    max_idx = i;
		}
	    }
	}
	if (i >= sz) {
	    //no unknown literals. so use the max dl literal
	    int v_idx = cl.literals()[max_idx].var_index();
	    int v_sign = cl.literals()[max_idx].var_sign();
	    variable(v_idx).ht_ptr(v_sign).push_back( & cl.literals()[max_idx]);
	    cl.literals()[max_idx].set_ht(1);
	    other_ht_idx = max_idx;
	}
	max_idx = -1; max_dl = -1;
	for (i=sz-1; i>=0; --i) {
	    if (i==other_ht_idx ) continue;
	    CLitPoolElement & l = cl.literals()[i];
	    int v_idx = cl.literals()[i].var_index();
	    my_var = & variable(v_idx);
	    if (variable(v_idx).value()==UNKNOWN) {
		int v_sign = cl.literals()[i].var_sign();
		variable(v_idx).ht_ptr(v_sign).push_back( & cl.literals()[i]);
		cl.literals()[i].set_ht(-1);
		break;
	    }
	    else {
		if (variable(v_idx).dlevel() > max_dl) {
		    max_dl = variable(v_idx).dlevel();
		    max_idx = i;
		}
	    }
	}
	if (i < 0) {
	    int v_idx = cl.literals()[max_idx].var_index();
	    int v_sign = cl.literals()[max_idx].var_sign();
	    CLitPoolElement * lit_ptr = & cl.literals()[max_idx];
	    variable(v_idx).ht_ptr(v_sign).push_back(lit_ptr);
	    cl.literals()[max_idx].set_ht(-1);
	}
    }
    //update some statistics
    ++_stats.num_added_clauses; 
    _stats.num_added_literals += n_lits;
    return new_cl;
}


void CDatabase::output_lit_pool_state (void) 
{
    cout << "Lit_Pool Used " << lit_pool_size() << " Free " << lit_pool_free_space()
	 << " Total " << lit_pool_size() + lit_pool_free_space()
	 << " Num. Cl " << num_clauses() << " Num. Lit " << num_literals(); 
    cout << " Efficiency " << (float)((float)num_literals()) / (float)((lit_pool_size() - num_clauses())) << endl;
}

#ifndef WIN32
void CDatabase::detail_dump_cl(ClauseIdx cl_idx, ostream & os ) {
#else
void CDatabase::detail_dump_cl(ClauseIdx cl_idx, ostream & os ) {
#endif
    os << "Clause : " << cl_idx;
    CClause & cl = clause(cl_idx);
    if (!cl.in_use()) 
	os << "\t\t\t======removed=====";
    char * value;
    int i, sz;
    sz = cl.num_lits(); 
    if (cl.num_lits() < 0) {
	os << ">> " ;
	sz = -sz;
    }
    for (i=0; i<sz; ++i) {
	if (literal_value(cl.literals()[i])==0) value = "0";
	else if (literal_value(cl.literals()[i])==1) value = "1";
	else value = "X";
	os << cl.literals()[i] << "(" << value << "@" << variable(cl.literal(i).var_index()).dlevel()<< ")  ";
    }
    os << endl;
}

#ifndef WIN32
void CDatabase::dump(ostream & os ) {
#else
void CDatabase::dump(ostream & os) {
#endif
    unsigned i;
    
    os << "Dump Database: " << endl;
    for(i=0; i<_clauses.size(); ++i) 
	detail_dump_cl(i);
//	    os << "Cl: " << i << " " << clause(i) << endl;
    for(i=1; i<_variables.size(); ++i)
	os << "VID: " << i << "\t" << variable(i);
}




















