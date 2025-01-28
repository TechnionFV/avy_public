//
// Created by dekel on 7/7/22.
//
#pragma once

#include <regex>
#include "sat/cnf/cnf.h"

static Gia_Man_t *loadAig(const std::string& fname) {
    Abc_Frame_t *pFrame = Abc_FrameGetGlobalFrame();

    string cmd = "read " + fname + " ; zero; fold2; &get -n";
    Cmd_CommandExecute(pFrame, cmd.c_str());

    Gia_Man_t * pAig = Abc_FrameReadGia(pFrame);
    return pAig;
}
/*
void convert_to_ascii(const std::string& fin, const std::string& fout){
    Abc_Frame_t *pFrame = Abc_FrameGetGlobalFrame();
    string rcmd = "read " + fin + " ; zero; &get -n";
    Cmd_CommandExecute(pFrame, rcmd.c_str());
    string wcmd = "write_aiger" + fout;
    Cmd_CommandExecute(pFrame, wcmd.c_str());
}
*/

static int condNum(char * ObjName){
    return stoi(regex_replace(ObjName, regex("[^0-9]*([0-9]+).*"), string("$1")));
}


static void Gia_clearMark0ForFaninRec(Gia_Obj_t *pObj){
    if(!pObj->fMark0){
        return;
    }
    pObj->fMark0=0;
    if(Gia_ObjIsCo(pObj)){
        Gia_clearMark0ForFaninRec(Gia_ObjFanin0(pObj));
    } else if(Gia_ObjIsAnd(pObj)){
        Gia_clearMark0ForFaninRec(Gia_ObjFanin0(pObj));
        Gia_clearMark0ForFaninRec(Gia_ObjFanin1(pObj));
    } else {
        assert(Gia_ObjIsCi(pObj));
    }
}
