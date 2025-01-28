//
// Created by dekel on 5/20/22.
//

#pragma once

#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <cassert>
#include <fstream>
#include <set>
#include <string>
#include <sstream>
#include <map>
#include <vector>

#include "base/abc/abc.h"
#include "aig/aig/aig.h"
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"
#include "aig/ioa/ioa.h"
#include "base/main/main.h"

#include <btor2parser/btor2parser.h>
#include <btor2aiger.h>

using namespace std;
using namespace abc;

struct meta {
    int cnt_app;
    int64_t btor_line;
    explicit meta(int64_t line) : cnt_app(0), btor_line(line){}
};

class MetaData
{
    Btor2Parser *parser;
    Btor2Model m_btor2_model;
    const char *model_path;

    map <int64_t, meta> btor_conds = {};
    map <int64_t, meta> gia_conds = {};
    map <int64_t, int64_t> var_to_satLit = {};
    map <int64_t, int64_t> aigSatLit_to_stateLit = {};
    map <int64_t, int64_t> stateLit_to_noStateLit = {};

public:
    string cond_prefix = "__cond_line_";
    vector<map<int64_t, bool>> assignments = {};

    explicit MetaData (const char *model_path) : model_path(model_path){
        FILE *model_file;
        if (!(model_file = fopen (model_path, "r"))) {
            std::cout << "fopen failed" << std::endl;
            printf("failed to open BTOR model file '%s' for reading", "\n");
            exit(EXIT_FAILURE);
        }

        parser = btor2parser_new ();
        if (!btor2parser_read_lines (parser, model_file)) {
            std::cout << "read_lines failed" << std::endl;
            const char *err = btor2parser_error (parser);
            std::cout << err << std::endl;
            fclose(model_file);
            exit(EXIT_FAILURE);
        }

        rewind(model_file);
        parse_btor2(model_file, m_btor2_model);

        fclose(model_file);
    }

    void collect_ite_conditions();
    Gia_Man_t* givemeAigWithMeta();

    Btor2Model& givemeBtor2Model() { return m_btor2_model; }

    map <int64_t, meta> get_map() {
        return btor_conds;
    }

    void print_btor_conditions () {
        cout << endl << "btor conditions lines: " << endl;
        for (auto const& [condNum, data] : btor_conds) {
            cout << condNum << " => appearances: " << data.cnt_app << "\t" << "btor line: " << data.btor_line << '\n';
        }
    }

    void print_gia_conditions () {
        cout << endl << "clean gia conditions obj: " << endl;
        for (auto const& [condNum, data] : gia_conds) {
            cout << condNum << "\t => appearances: " << data.cnt_app << "\t" << "btor line: "  << data.btor_line << '\n';
        }
    }

    void print_assignments () {
        cout << endl << "valid assignments: " << endl;
        for (const auto& ass : assignments){
            for (auto const& [obj, val] : ass){
                cout << obj << ": " << val << "\t";
            }
            cout << "\n";
        }
    }

    int64_t satCoLit_to_noStateLit(int i){
        return stateLit_to_noStateLit[aigSatLit_to_stateLit[i]];
    }

    //aigUtils
    Gia_Man_t * Gia_remove_condStates(Gia_Man_t *p);
    Gia_Man_t * Gia_DupUnMarked( Gia_Man_t * p );
    Gia_Man_t * Gia_make_condSAT(Gia_Man_t *p);
    void find_assignments(Gia_Man_t * p);
    void generate_assignments(Gia_Man_t *p);
    Gia_Man_t * gia_per_assignment(Gia_Man_t * p, const map<int64_t, bool>& ass);

private:
    void add_conditions_states ();

};