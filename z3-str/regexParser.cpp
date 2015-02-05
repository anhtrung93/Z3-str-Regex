#include "strTheory.h"

/*
 * OWN CODE
 * Parse for Regex with form <set>
 */
Z3_ast parseBraces(Z3_theory t, std::string strInBraces, Z3_ast & assert){
    if (strInBraces[0] != '[' || strInBraces[strInBraces.length() - 1] != ']'){
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> parseBraces(): %s invalid regex-brace Type\n", strInBraces.c_str());
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
Z3_ast parseStar(Z3_theory t, std::string regexStr, Z3_ast & breakDownAssert){
  if (regexStr[regexStr.length() - 1] != '?'){
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> parseStar(): %s invalid regex-star Type\n", regexStr.c_str());
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
      __debugPrint(logFile, ">> parseStar(): %s invalid regex-star Type\n", regexStr.c_str());
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
      __debugPrint(logFile, ">> parsePlus(): %s invalid regex-plus Type\n", regexStr.c_str());
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
      __debugPrint(logFile, ">> parseCounter(): %s invalid regex-counter Type\n", regexStr.c_str());
#endif
    return NULL;
  }
  int id = regexStr.length() - 1;
  while (id >= 0 && regexStr[id] != '{'){
    -- id;
  }
  if (id < 0){
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> parseCounter(): %s invalid regex-counter Type\n", regexStr.c_str());
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
    result = mk_star(t, my_mk_regex_value(t, regexStr.c_str()), mk_int(ctx, repeatTimes));
  }
  
  return result;
}

/*
 * OWN CODE
 */
Z3_ast regex_parse(Z3_theory t, std::string regexStr, Z3_ast & breakDownAssert){
  return parseCounter(t, regexStr, breakDownAssert);
  /*Z3_context ctx = Z3_theory_get_context(t);
  std::size_t specChar = regexStr.find_first_of("[(|");
  //TODO rewrite below code
  if (specChar != std::string::npos){
    if (regexStr[specChar] == '|'){
      Z3_ast subRegex[2], subAssert[2];
      std::string firstStr = regexStr.substr(0, specChar);
      std::string lastStr = regexStr.substr(specChar + 1);
      subRegex[0] = regex_parse(t, firstStr, subAssert[0]);    
      subRegex[1] = regex_parse(t, lastStr, subAssert[1]);

      Z3_ast result = my_mk_internal_string_var(t);
      subAssert[0] = mk_2_and(t, Z3_mk_eq(ctx, result, subRegex[0]), subAssert[0]);
      subAssert[1] = mk_2_and(t, Z3_mk_eq(ctx, result, subRegex[1]), subAssert[1]);
      breakDownAssert = Z3_mk_or(ctx, 2, subAssert);
      return result;
    } else if (regexStr[specChar] == '['){
      std::size_t closeBracket = regexStr.find(']', specChar + 1);//+1 to eliminate case []dfasdf]
      Z3_ast assert[3], result[3];
  
      std::string firstStr = regexStr.substr(0, specChar);
      std::string lastStr = regexStr.substr(closeBracket + 1);
      std::string listChar = regexStr.substr(specChar + 1, closeBracket - specChar - 1);
      result[0] = regex_parse(t, firstStr, assert[0]);    
      result[2] = regex_parse(t, lastStr, assert[2]);
      result[1] = parseBraces(t, listChar, assert[1]);
  
      breakDownAssert = Z3_mk_and(ctx, 3, assert);
      return mk_concat(t, result[0], mk_concat(t, result[1], result[2]));
    } else { //if (regexStr[specChar] == '(')
      std::size_t closeParenthesis = regexStr.find(')', specChar);
      Z3_ast assert[3], result[3];
  
      std::string firstStr = regexStr.substr(0, specChar);
      std::string lastStr = regexStr.substr(closeParenthesis + 1);
      std::string middleStr = regexStr.substr(specChar + 1, closeParenthesis - specChar - 1);
      result[0] = regex_parse(t, firstStr, assert[0]);    
      result[2] = regex_parse(t, lastStr, assert[2]);
      result[1] = regex_parse(t, middleStr, assert[1]);
  
      breakDownAssert = Z3_mk_and(ctx, 3, assert);
      return mk_concat(t, result[0], mk_concat(t, result[1], result[2]));
    }
  } else {
    breakDownAssert = Z3_mk_true(ctx);
    return my_mk_str_value(t, regexStr.c_str());
  }*/
}

