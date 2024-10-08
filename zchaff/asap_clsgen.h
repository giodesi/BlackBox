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


#ifndef __CLAUSE_GENERATOR__
#define __CLAUSE_GENERATOR__
#include <vector>
#include "asap_solver.h"
class CClause_Gen {
private:
    int pos(int i) 
	{ 
	    return i;
	}
    int neg(int i) 
	{
	    return i^0x1;
	}
public:
    void and2 (CSolver & solver, int a, int b, int o) 
	{
	    // a*b=c <==> (a + o')( b + o')(a'+b'+o)
	    vector <int> lits;

	    lits.clear();
	    lits.push_back(pos(a));
	    lits.push_back(neg(o));
	    solver.add_clause(&(*lits.begin()), lits.size());

	    lits.clear();
	    lits.push_back(pos(b));
	    lits.push_back(neg(o));
	    solver.add_clause(&(*lits.begin()), lits.size());

	    lits.clear();
	    lits.push_back(neg(a));
	    lits.push_back(neg(b));
	    lits.push_back(pos(o));
	    solver.add_clause(&(*lits.begin()), lits.size());
	}

    void and_n (CSolver & solver, int * inputs, int num_input, int o)
	{
            int i;
	    vector <int> lits;
	    for (i=0; i< num_input; ++i) {
		lits.clear();
		lits.push_back(pos(inputs[i]));
		lits.push_back(neg(o));
		solver.add_clause(&(*lits.begin()), lits.size());
	    }
	    lits.clear();
	    for (i=0; i< num_input; ++i)
		lits.push_back(neg(inputs[i]));
	    lits.push_back(pos(o));
	    solver.add_clause(&(*lits.begin()), lits.size());
	    
	}

    void or2 (CSolver & solver, int a, int b, int o)
	{
	    // a+b=c <==> (a' + c)( b' + c)(a + b + c')
	    vector <int> lits;

	    lits.clear();
	    lits.push_back(neg(a));
	    lits.push_back(pos(o));
	    solver.add_clause(&(*lits.begin()), lits.size());

	    lits.clear();
	    lits.push_back(neg(b));
	    lits.push_back(pos(o));
	    solver.add_clause(&(*lits.begin()), lits.size());

	    lits.clear();
	    lits.push_back(pos(a));
	    lits.push_back(pos(b));
	    lits.push_back(neg(o));
	    solver.add_clause(&(*lits.begin()), lits.size());
	}

    void or_n (CSolver & solver, int * inputs, int num_input, int o)
	{
            int i;
	    vector <int> lits;
	    for (i=0; i< num_input; ++i) {
		lits.clear();
		lits.push_back(neg(inputs[i]));
		lits.push_back(pos(o));
		solver.add_clause(&(*lits.begin()), lits.size());
	    }
	    lits.clear();
	    for (i=0; i< num_input; ++i)
		lits.push_back(pos(inputs[i]));
	    lits.push_back(neg(o));
	    solver.add_clause(&(*lits.begin()), lits.size());
	    
	}

    void nand2 (CSolver & solver, int a, int b, int o)
	{
	    // a Nand b = o <==> (a + o)( b + o)(a' + b' + o')
	    vector <int> lits;

	    lits.clear();
	    lits.push_back(pos(a));
	    lits.push_back(pos(o));
	    solver.add_clause(&(*lits.begin()), lits.size());

	    lits.clear();
	    lits.push_back(pos(b));
	    lits.push_back(pos(o));
	    solver.add_clause(&(*lits.begin()), lits.size());

	    lits.clear();
	    lits.push_back(neg(a));
	    lits.push_back(neg(b));
	    lits.push_back(neg(o));
	    solver.add_clause(&(*lits.begin()), lits.size());
	}

    void nand_n(CSolver & solver, int * inputs, int num_input, int o)
	{
            int i;
            
	    vector <int> lits;
	    for (i=0; i< num_input; ++i) {
		lits.clear();
		lits.push_back(pos(inputs[i]));
		lits.push_back(pos(o));
		solver.add_clause(&(*lits.begin()), lits.size());
	    }
	    lits.clear();
	    for (i=0; i< num_input; ++i)
		lits.push_back(neg(inputs[i]));
	    lits.push_back(neg(o));
	    solver.add_clause(&(*lits.begin()), lits.size());
	    
	}

    void nor2 (CSolver & solver, int a, int b, int o)
	{
	    // a Nor b = o <==> (a' + o')( b' + o')(a + b + o)
	    vector <int> lits;

	    lits.clear();
	    lits.push_back(neg(a));
	    lits.push_back(neg(o));
	    solver.add_clause(&(*lits.begin()), lits.size());

	    lits.clear();
	    lits.push_back(neg(b));
	    lits.push_back(neg(o));
	    solver.add_clause(&(*lits.begin()), lits.size());

	    lits.clear();
	    lits.push_back(pos(a));
	    lits.push_back(pos(b));
	    lits.push_back(pos(o));
	    solver.add_clause(&(*lits.begin()), lits.size());
	}
   
    void nor_n (CSolver & solver, int * inputs, int num_input, int o)
	{
            int i;
            
	    vector <int> lits;
	    for (i=0; i< num_input; ++i) {
		lits.clear();
		lits.push_back(neg(inputs[i]));
		lits.push_back(neg(o));
		solver.add_clause(&(*lits.begin()), lits.size());
	    }
	    lits.clear();
	    for (i=0; i< num_input; ++i)
		lits.push_back(pos(inputs[i]));
	    lits.push_back(pos(o));
	    solver.add_clause(&(*lits.begin()), lits.size());
	    
	}

    void xor2 (CSolver & solver, int a, int b, int o)
	{
	    // a xor b = o <==> (a' + b' + o')
	    //                  (a + b + o' )
	    //                  (a' + b + o)
	    // 	                (a + b' + o)
	    vector <int> lits;

	    lits.clear();
	    lits.push_back(neg(a));
	    lits.push_back(neg(b));
	    lits.push_back(neg(o));
	    solver.add_clause(&(*lits.begin()), lits.size());

	    lits.clear();
	    lits.push_back(pos(a));
	    lits.push_back(pos(b));
	    lits.push_back(neg(o));
	    solver.add_clause(&(*lits.begin()), lits.size());

	    lits.clear();
	    lits.push_back(neg(a));
	    lits.push_back(pos(b));
	    lits.push_back(pos(o));
	    solver.add_clause(&(*lits.begin()), lits.size());

	    lits.clear();
	    lits.push_back(pos(a));
	    lits.push_back(neg(b));
	    lits.push_back(pos(o));
	    solver.add_clause(&(*lits.begin()), lits.size());
	}

    void not1 (CSolver & solver, int a, int o)
	{
	    // a' = o <==> (a' + o')( a + o)
	    vector <int> lits;

	    lits.clear();
	    lits.push_back(neg(a));
	    lits.push_back(neg(o));
	    solver.add_clause(&(*lits.begin()), lits.size());

	    lits.clear();
	    lits.push_back(pos(a));
	    lits.push_back(pos(o));
	    solver.add_clause(&(*lits.begin()), lits.size());
	}
};


#endif







