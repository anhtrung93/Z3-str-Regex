#include "strTheory.h"

/*
 * OWN CODE
 * Parse for Regex with form <set>
 */
Z3_ast parseBraces(Z3_theory t, std::string strInBraces, Z3_ast & assert){
  assert = NULL;
  if (strInBraces[0] != '[' || strInBraces[strInBraces.length() - 1] != ']'){
#ifdef DEBUGLOG
   __debugPrint(logFile, ">> parseBraces(): %s invalid regex-brace Type %d\n", strInBraces.c_str(), __LINE__);
#endif
    return NULL;
  }
  strInBraces = strInBraces.substr(1, strInBraces.length() - 2);
    
  Z3_context ctx = Z3_theory_get_context(t);
  std::set<Z3_ast> item_set;
  Z3_ast character = my_mk_internal_string_var(t);
  bool startsWithCaret = false;
  if (strInBraces[0] == '^'){
    startsWithCaret = true;
    strInBraces = strInBraces.substr(1);
  }
  //TODO process for special character in the dictionary 
  for (unsigned int id = 0; id < strInBraces.length(); ++ id){
    if (strInBraces[id] == '-' && id < strInBraces.length() - 1 && id > 0){
    	char charTemp;
      //becareful with 4 below lines
      for (charTemp = strInBraces[id - 1] + 1; charTemp <= strInBraces[id + 1]; ++ charTemp){
        strInBraces[id - 1] = charTemp;
        item_set.insert(my_mk_str_value(t, strInBraces.substr(id - 1, 1).c_str()));
      }
      ++id;
    } else {
      item_set.insert(my_mk_str_value(t, strInBraces.substr(id, 1).c_str()));
    }
  }
  std::set<Z3_ast>::iterator it;
  Z3_ast * or_items = new Z3_ast [item_set.size()];
  int pos; 
  for (it = item_set.begin(), pos = 0; it != item_set.end(); ++ it, ++ pos){
    or_items[pos] = Z3_mk_eq(ctx, character, *it); 
  }
  Z3_ast result = character; assert = Z3_mk_or(ctx, pos, or_items);
  if (startsWithCaret){
    assert = Z3_mk_not(ctx, assert);  
  }    
  Z3_ast charLen_eq_one = Z3_mk_eq(ctx, mk_int(ctx, 1), mk_length(t, character));
  assert = mk_2_and(t, charLen_eq_one, assert);
 
  delete[] or_items;
  return result;
}

/*
 * OWN CODE
 * parse for regex with form <question>
 */
Z3_ast parseQuestion(Z3_theory t, std::string regexStr, Z3_ast & breakDownAssert){
  if (regexStr[regexStr.length() - 1] != '?'){
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> parseQuestion(): %s invalid regex-question Type %d\n", regexStr.c_str(), __LINE__);
#endif
    return NULL;
  }
  regexStr = regexStr.substr(0, regexStr.length() - 1);
  
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast result = my_mk_internal_string_var(t);
  
  Z3_ast assert = NULL;
  Z3_ast exist = regex_parse(t, regexStr, assert);
  assert = mk_2_and(t, assert, Z3_mk_eq(ctx, result, exist));
  Z3_ast notExist = my_mk_str_value(t, "");
  breakDownAssert = mk_2_or(t, assert, Z3_mk_eq(ctx, result, notExist));
  
  return result;
}


/*
 * OWN CODE
 * parse for regex with form <star>
 */
Z3_ast parseStar(Z3_theory t, std::string regexStr, Z3_ast & breakDownAssert){
  if (regexStr[regexStr.length() - 1] != '*'){
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> parseStar(): %s invalid regex-star Type %d\n", regexStr.c_str(), __LINE__);
#endif
    return NULL;
  }
  regexStr = regexStr.substr(0, regexStr.length() - 1);
  
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast intVar = my_mk_internal_int_var(t);
  breakDownAssert = Z3_mk_ge(ctx, intVar, mk_int(ctx, 0));
  Z3_ast result = mk_star(t, my_mk_regex_value(t, regexStr.c_str()), intVar);
  
  return result;
}

/*
 * OWN CODE
 * parse for regex with form <plus>
 */
Z3_ast parsePlus(Z3_theory t, std::string regexStr, Z3_ast & breakDownAssert){
  if (regexStr[regexStr.length() - 1] != '+'){
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> parsePlus(): %s invalid regex-plus Type %d\n", regexStr.c_str(), __LINE__);
#endif
    return NULL;
  }
  regexStr = regexStr.substr(0, regexStr.length() - 1);
  
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast intVar = my_mk_internal_int_var(t);
  breakDownAssert = Z3_mk_ge(ctx, intVar, mk_int(ctx, 1));
  Z3_ast result = mk_star(t, my_mk_regex_value(t, regexStr.c_str()), intVar);
  
  return result;
}

/*
 * OWN CODE
 * parse for regex with form <counter>
 */
Z3_ast parseCounter(Z3_theory t, std::string regexStr, Z3_ast & breakDownAssert){
  if (regexStr[regexStr.length() - 1] != '}'){
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> parseCounter(): %s invalid regex-counter Type %d\n", regexStr.c_str(), __LINE__);
#endif
    return NULL;
  }
  int id = regexStr.length() - 1;
  while (id >= 0 && regexStr[id] != '{'){
    -- id;
  }
  if (id < 0){
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> parseCounter(): %s invalid regex-counter Type %d\n", regexStr.c_str(), __LINE__);
#endif
    return NULL;
  }
  std::string counterStr = regexStr.substr(id + 1, regexStr.length() - id - 2);  
  regexStr = regexStr.substr(0, id);  
  Z3_context ctx = Z3_theory_get_context(t);

  Z3_ast result = NULL;  
  int temp = (int) counterStr.find_first_of(",");
  if (temp != (int) std::string::npos){
    Z3_ast intVar = my_mk_internal_int_var(t);
  
    int first = atoi(counterStr.substr(0, temp).c_str());
    breakDownAssert = Z3_mk_ge(ctx, intVar, mk_int(ctx, first));
    if (temp + 1 == (int) counterStr.length()){
    } else {
      int second = atoi(counterStr.substr(temp + 1, counterStr.length() - temp - 1).c_str());
      breakDownAssert = mk_2_and(t, breakDownAssert, Z3_mk_le(ctx, intVar, mk_int(ctx, second)));
    }
    result = mk_star(t, my_mk_regex_value(t, regexStr.c_str()), intVar);
    
  } else {
    int repeatTimes = atoi(counterStr.c_str());
    std::string new_regex = "";
    for (int id = 0; id < repeatTimes; ++ id){
      new_regex += regexStr;
    }
    result = regex_parse(t, new_regex, breakDownAssert);
  }
  
  return result;
}

/*
 * OWN CODE
 * parse for regex with form <group>
 */
Z3_ast parseGroup(Z3_theory t, std::string regexStr, Z3_ast & assert){
  if (regexStr[0] != '(' || regexStr[regexStr.length() - 1] != ')'){
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> parseGroup(): %s invalid regex-group Type %d\n", regexStr.c_str(), __LINE__);
#endif
    return NULL;
  }
  regexStr = regexStr.substr(1, regexStr.length() - 2);
  
  return regex_parse(t, regexStr, assert);
}

/*
 * OWN CODE
 * parse special characters
 */
Z3_ast parseSpecialCharacter(Z3_theory t, std::string regexStr, Z3_ast & assert){
  if (regexStr[0] != '.' || regexStr.length() != 2 || regexStr[0] != '\\'){
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> parseSpecialCharacter(): %s invalid regex-specialChar Type %d\n", regexStr.c_str(), __LINE__);
#endif    
    return NULL;
  }
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast result = NULL;
  if (regexStr[0] == '.' && regexStr.length() == 1){
    result = my_mk_internal_string_var(t);
    assert = Z3_mk_eq(ctx, mk_length(t, result), mk_int(ctx, 1));
  } else if (regexStr[1] == 'w'){  //TODO    
  } else if (regexStr[1] == 'W'){
  } else if (regexStr[1] == 'd'){
  } else if (regexStr[1] == 'D'){
  } else if (regexStr[1] == 's'){
  } else if (regexStr[1] == 'S'){
  }
  
  return result;
}

/*
 * OWN CODE
 * parse for regex with form <union>
 */
/*Z3_ast parseUnion(Z3_theory t, std::string regexStr, Z3_ast & assert){
  int unionCharId = (int) regexStr.find("|");
  if (unionCharId == (int) std::string::npos){
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> parseUnion(): %s invalid regex-union Type %d\n", regexStr.c_str(), __LINE__);
#endif
    return NULL;
  }
  std::string first = regexStr.substr(0, unionCharId);
  std::string second = regexStr.substr(unionCharId + 1, regexStr.length() - unionCharId - 1);
  Z3_context ctx = Z3_theory_get_context(t);  
  
  Z3_ast result = my_mk_internal_string_var(t);
  Z3_ast assert1 = Z3_mk_eq(ctx, result, my_mk_str_value(t, first.c_str()));
  Z3_ast assert2 = Z3_mk_eq(ctx, result, my_mk_str_value(t, second.c_str()));
  assert = mk_2_or(t, assert1, assert2);
  
  return result;
} */
 
/*
 * OWN CODE
 */
Z3_ast regex_parse(Z3_theory t, std::string regexStr, Z3_ast & breakDownAssert){
  breakDownAssert = NULL;
  Z3_context ctx = Z3_theory_get_context(t);
  if (regexStr.size() == 0){
    return my_mk_str_value(t, "");
  }
  std::stack<std::string> components;
  for (int id = 0; id < (int) regexStr.length(); ++ id){
    //TODO 
    if (regexStr[id] == '*' || regexStr[id] == '?' || regexStr[id] == '+'){
      if (components.size() <= 0){
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> regex_parse(): %s invalid Type %d\n", regexStr.c_str(), __LINE__);
#endif      
        return NULL;
      } else {
        std::string temp = components.top() + regexStr.substr(id, 1); 
        components.pop();
/*#ifdef DEBUGLOG
      __debugPrint(logFile, ">> regex_parse(): push %s %d\n", temp.c_str(), __LINE__);
#endif    */      
        components.push(temp);
      }
    } else if (regexStr[id] == ']' || regexStr[id] == '}' || regexStr[id] == ')'){
      char tempChar;
      if (regexStr[id] == ']') { tempChar = '['; }
      else if (regexStr[id] == '}') { tempChar = '{'; }
      else { tempChar = '('; }
      
      std::string in;
      std::string tempStr = regexStr.substr(id, 1);
      do {
        if (components.size() <= 0){
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> regex_parse(): %s invalid Type %d\n", regexStr.c_str(), __LINE__);
#endif      
        return NULL;
        }
        in = components.top();
        tempStr = in + tempStr;
        components.pop();
      } while (in[0] != tempChar || in.size() != 1);
      if (tempChar == '{'){
        tempStr = components.top() + tempStr;
        components.pop();
      }
/*#ifdef DEBUGLOG
      __debugPrint(logFile, ">> regex_parse(): push %s %d\n", tempStr.c_str(), __LINE__);
#endif          */
      components.push(tempStr);
    } else {
/*#ifdef DEBUGLOG
      __debugPrint(logFile, ">> regex_parse(): push %s %d\n", regexStr.substr(id, 1).c_str(), __LINE__);
#endif  */
      components.push(regexStr.substr(id, 1));
    }
  }
  Z3_ast currentAst = NULL;
  std::set<Z3_ast> or_list;
  std::set<Z3_ast> assert_list;
  while (! components.empty()){
    std::string tempStr = components.top();
    components.pop();
    if (tempStr.size() == 1 && tempStr[0] == '|'){
      or_list.insert(currentAst);
      currentAst = NULL;
    } else {
      Z3_ast strAst = NULL;
      if (isSimpleRegex(tempStr)){
        while (! components.empty() && isSimpleRegex(components.top())){
          tempStr = components.top() + tempStr;
          components.pop();
        }
        strAst = my_mk_str_value(t, tempStr.c_str());
      } else {
        char lastTempStr = tempStr[tempStr.length() - 1];
        Z3_ast assert = NULL;
        if (lastTempStr == '*'){
          strAst = parseStar(t, tempStr, assert);
        } else if (lastTempStr == '+'){
          strAst = parsePlus(t, tempStr, assert);
        } else if (lastTempStr == '?'){
          strAst = parseQuestion(t, tempStr, assert);
        } else if (lastTempStr == ']'){
          strAst = parseBraces(t, tempStr, assert);
        } else if (lastTempStr == '}'){
          strAst = parseCounter(t, tempStr, assert);
        } else if (lastTempStr == ')'){
          strAst = parseGroup(t, tempStr, assert);
        } else {
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> regex_parse(): unknown components %s %d\n\n", tempStr.c_str(), __LINE__);
#endif        
        }
        if (assert != NULL){
          assert_list.insert(assert);
        }
      }
      if (currentAst == NULL){
        currentAst = strAst;
      } else {
        if (currentAst == NULL){
          // must meet unknown components
        } else {
          currentAst = mk_concat(t, strAst, currentAst);
        }
      }
#ifdef DEBUGLOG
    __debugPrint(logFile, ">> regex_parse(): currentAst = %d ", __LINE__);
    printZ3Node(t, currentAst);
    __debugPrint(logFile, "\n\n");
#endif            
    }      
  }

  or_list.insert(currentAst);
  if (assert_list.size() > 0){
    Z3_ast * assert = new Z3_ast[assert_list.size()];
    std::set<Z3_ast>::iterator it; int pos;
    for (it = assert_list.begin(), pos = 0; it != assert_list.end(); ++ it, ++ pos){
      assert[pos] = *it;
    }
    breakDownAssert = Z3_mk_and(ctx, assert_list.size(), assert);
    delete[] assert;
  }

  Z3_ast result = NULL;
  if (or_list.size() > 1){
    result = my_mk_internal_string_var(t);
    Z3_ast * ors = new Z3_ast[or_list.size()];
    std::set<Z3_ast>::iterator it; int pos;
    for (it = or_list.begin(), pos = 0; it != or_list.end(); ++ it, ++ pos){
      ors[pos] = Z3_mk_eq(ctx, result, *it);
    }
    breakDownAssert = mk_2_and(t, breakDownAssert, Z3_mk_or(ctx, or_list.size(), ors));
    delete[] ors;
  } else {
    result = currentAst;
  }
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> regex_parse(): %d\n", __LINE__);
      printZ3Node(t, result);
      __debugPrint(logFile, "\n and assert: ");
      printZ3Node(t, breakDownAssert);
      __debugPrint(logFile, "\n\n");
#endif          
  return result;
}

bool isSimpleRegex(std::string regexStr){//TODO
  if (regexStr.find_first_of("*+?[](){}|") == std::string::npos){
    return true;
  } else {
    return false;
  }
}

