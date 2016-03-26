#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0
//My code
typedef vector<vector<int> > intMatrix;
//
uint numVars;
uint numClauses;
vector<vector<int> > clauses;
vector<int> model;
vector<int> modelStack;
uint indexOfNextLitToPropagate;
uint decisionLevel;

//My code
uint propagations;
uint decisions;

intMatrix positiveClauses;
intMatrix negativeClauses;
vector<int> conflicts;
//

void readClauses( ){
  // Skip comments
  char c = cin.get();
  while (c == 'c') {
    while (c != '\n') c = cin.get();
    c = cin.get();
  }  
  // Read "cnf numVars numClauses"
  string aux;
  cin >> aux >> numVars >> numClauses;
  clauses.resize(numClauses);
  //My code
  positiveClauses.resize(numClauses+1);
  negativeClauses.resize(numClauses+1);
  conflicts.resize(numClauses+1,0); // Todos a 0, inicialmente no hay conflictos
  //
 
  // Read clauses
  for (uint i = 0; i < numClauses; ++i) {
    int lit;
    while (cin >> lit and lit != 0) clauses[i].push_back(lit);
    //My code
    for(uint j = i; j > 0; --j) { //Ordenamos de mayor a menor [MergeSort???]
      if(clauses[j-1].size() > clauses[j].size()) swap(clauses[j-1], clauses[j]);
      else break; 
    }
    //
  }
  //My code
    //
  for( uint j = 0; j < numClauses; ++j ) {
    for( uint k = 0; k < clauses[j].size(); ++k ) {
      uint literal = clauses[j][k];
      if(literal >= 0) {
        positiveClauses[literal].push_back(j);  
      }
      else {
        negativeClauses[literal].push_back(j);
      }
      ++conflicts[literal];
    }
  }
  //    
}



int currentValueInModel(int lit){
  if (lit >= 0) return model[lit];
  else {
    if (model[-lit] == UNDEF) return UNDEF;
    else return 1 - model[-lit];
  }
}


void setLiteralToTrue(int lit){
  modelStack.push_back(lit);
  if (lit > 0) model[lit] = TRUE;
  else model[-lit] = FALSE;		
}

//My code
bool propagateGivesConflict ( ) {
  int     literal;
  bool    someLitTrue;
  int     numUndefs;
  int     lastLitUndef;
  int     pos;
  int     val;
  int     auxLiteral;
  while ( indexOfNextLitToPropagate < modelStack.size() ) {
    literal = modelStack[indexOfNextLitToPropagate];
    if( literal < 0 ) {
      for( uint i = 0; i < positiveClauses[-literal].size(); ++i ) {
        ++propagations;
        someLitTrue = false;
        numUndefs = 0;
        lastLitUndef = 0;
        pos = positiveClauses[-literal][i];
        for( uint k = 0; not someLitTrue and k < clauses[pos].size(); ++k ){
  	      val = currentValueInModel( clauses[pos][k] );
  	      if( val == TRUE ) {
            someLitTrue = true;
  	      }
          else if( val == UNDEF ){ 
            ++numUndefs; 
            lastLitUndef = clauses[pos][k]; 
          }
        }
        if( not someLitTrue and numUndefs == 0 ) {
          ++conflicts[-literal];
          return true; // conflict! all lits false
        }
        else if ( not someLitTrue and numUndefs == 1 ) {
          setLiteralToTrue( lastLitUndef );	
        }
      }
    }
    else {
      for( uint i = 0; i < negativeClauses[literal].size(); ++i) {
        someLitTrue = false;
        numUndefs = 0;
        lastLitUndef = 0;
        pos = negativeClauses[literal][i];
        for( uint k = 0; not someLitTrue and k < clauses[pos].size(); ++k ) {
          val = currentValueInModel( clauses[pos][k] );
          if( val == TRUE ) {
            someLitTrue = true;
          }
          else if( val == UNDEF ){
            ++numUndefs;
            lastLitUndef = clauses[pos][k];
          }
        }
        if( not someLitTrue and numUndefs == 0) {
          for( int l = 0; l < clauses[pos].size(); ++l ) {
            auxLiteral = clauses[pos][l];
            if( auxLiteral < 0 ) {
              ++conflicts[-auxLiteral];
            }
            else {
              ++conflicts[auxLiteral];
            }
          }
          return true;
        }
        else if( not someLitTrue and numUndefs == 1 ) {
          setLiteralToTrue(lastLitUndef);
        }
      }
    }
    ++indexOfNextLitToPropagate;    
  }
  return false;
}

//

void backtrack(){
  uint i = modelStack.size() -1;
  int lit = 0;
  while (modelStack[i] != 0){ // 0 is the DL mark
    lit = modelStack[i];
    model[abs(lit)] = UNDEF;
    modelStack.pop_back();
    --i;
  }
  // at this point, lit is the last decision
  modelStack.pop_back(); // remove the DL mark
  --decisionLevel;
  indexOfNextLitToPropagate = modelStack.size();
  setLiteralToTrue(-lit);  // reverse last decision
}


// Heuristic for finding the next decision literal:
//My code
int getNextDecisionLiteral(){
  int aux = 0;
  int max = 0;
  for( int i = 1; i < numVars; ++i ) {
    if( conflicts[i] > max ) {
      max = conflicts[i];
    }
    if( model[i] == UNDEF and ( aux == 0 or conflicts[i] > conflicts[aux] ) ) {
      aux = i;
    } 
  }
  if( max > numClauses ) {
    for( int j = 1; j < numVars; ++j ) {
      conflicts[j] /= 2;
    }
  }
  return aux; 
}
//
void checkmodel(){
  for (int i = 0; i < numClauses; ++i){
    bool someTrue = false;
    for (int j = 0; not someTrue and j < clauses[i].size(); ++j)
      someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
    if (not someTrue) {
      cout << "Error in model, clause is not satisfied:";
      for (int j = 0; j < clauses[i].size(); ++j) cout << clauses[i][j] << " ";
      cout << endl;
      exit(1);
    }
  }  
}

int main(){ 
  time_t now;
  time_t now2;
  float seconds;

  readClauses(); // reads numVars, numClauses and clauses
  model.resize( numVars+1, UNDEF );
  indexOfNextLitToPropagate = 0;  
  decisionLevel = 0;

  decisions = 0;
  propagations = 0;
  time( &now );

  // Take care of initial unit clauses, if any
  for( uint i = 0; i < numClauses; ++i ) {
    if( clauses[i].size() == 1 ) {
      int lit = clauses[i][0];
      int val = currentValueInModel( lit );
      if( val == FALSE ) {
        time( &now2 );
        seconds = difftime( now2, now );
        cout << "s UNSATISFIABLE" << endl;
        cout << "c "<< seconds << " seconds total run time"  << endl;
        cout << "c "<< propagations << " propagations" << endl;
        cout << "c "<< ( uint )propagations/( seconds*1000000 ) << " megaprops/second" << endl;
        cout << "c "<< decisions << " decisions"  << endl;
        return 10;
      }
      else if( val == UNDEF ) setLiteralToTrue( lit );
    }
  }
  // DPLL algorithm
  while( true ) {
    while( propagateGivesConflict() ) {
      if( decisionLevel == 0 ) {
        time( &now2 );
        seconds = difftime( now2, now );
        cout << "s UNSATISFIABLE" << endl;
        cout << "c "<< seconds << " seconds total run time"  << endl;
        cout << "c "<< propagations << " propagations" << endl;
        cout << "c "<< ( uint )propagations/( seconds*1000000 ) << " megaprops/second" << endl;
        cout << "c "<< decisions << " decisions"  << endl;
        return 10;
      }
      backtrack();
    }
    int decisionLit = getNextDecisionLiteral();
    if (decisionLit == 0) {
      time(&now2);
      seconds = difftime(now2, now);
      checkmodel();
      cout << "s SATISFIABLE" << endl;
      cout << "c "<< seconds << " seconds total run time"  << endl;
      cout << "c "<< propagations << " propagations" << endl;
      cout << "c "<< (uint)propagations/(seconds*1000000) << " megaprops/second" << endl;
      cout << "c "<< decisions << " decisions"  << endl;
      return 20; 
    }
    // start new decision level:
    modelStack.push_back(0);  // push mark indicating new DL
    ++indexOfNextLitToPropagate;
    ++decisionLevel;
    setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
  }
}