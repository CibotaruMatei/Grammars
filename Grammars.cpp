#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <vector>

std::string replace(std::string s, char a, char b) {
    for (int i = 0; i < s.size(); i++) {
        if (s[i] == a) s[i] = b;
    }
    return s;
}

struct grammar {
    char init = 'S';
    std::set<char> terminals, nonterminals;
    std::map<char, std::set<std::string>> rules;
};

void read(grammar& g, std::istream& in) {
    in >> g.init;
    int n;
    in >> n;
    for (int i = 0; i < n; i++) {
        char x;
        in >> x;
        g.nonterminals.insert(x);
        g.rules.emplace(x, std::set<std::string>());
    }
    in >> n;
    for (int i = 0; i < n; i++) {
        char x;
        in >> x;
        g.terminals.insert(x);
    }
    in >> n;
    for (int i = 0; i < n; i++) {
        char x;
        std::string s;
        in >> x >> s;
        g.rules[x].insert(s);
    }
}

void write(grammar& g, std::ostream& out) {
    out << g.init << "\n" << g.nonterminals.size() << "\n";
    for (auto& i : g.nonterminals) {
        out << i << " ";
    }
    out << "\n" << g.terminals.size() << "\n";
    for (auto& i : g.terminals) {
        out << i << " ";
    }
    for (auto& i : g.nonterminals) {
        out << "\n";
        out << i << " -> ";
        for (auto& j : g.rules[i]) {
            out << j << " ";
        }
    }
    out << "\n";
}

char addNonterminal(grammar& g) {
    char c;
    for (c = 'A'; c <= 'Z'; c++)
        if (g.nonterminals.find(c) == g.nonterminals.end()) {
            g.nonterminals.insert(c);
            g.rules.emplace(c, std::set<std::string>());
            break;
        }
    return c;
}

char getLambda(grammar& g) {
    for (auto& N : g.nonterminals) {
        for (std::set<std::string>::iterator it = g.rules[N].begin(); it != g.rules[N].end(); ++it) {
            if (*it == "$") return N;
        }
    }
    return '$';
}

void lambdaElim(grammar& g) {
    char key = getLambda(g);

    while (key != '$') {
        if (g.rules[key].size() == 1) {
            g.nonterminals.erase(key);
            g.rules.erase(key);

            for (auto& N : g.nonterminals) {
                std::set<std::string> aux;
                for (auto& s : g.rules[N]) {
                    std::string cpy = s;
                    if (cpy.find(key) != std::string::npos) {
                        if (cpy.size() == 1) {
                            aux.insert("$");
                        }
                        else {
                            aux.insert(cpy.substr(0, cpy.find('$')) + cpy.substr(cpy.find('$') + 1, cpy.size()));
                        }
                    }
                    else aux.insert(cpy);
                }
                g.rules[N] = aux;
            }
        }
        else {
            g.rules[key].erase("$");

            for (auto& N : g.nonterminals) {
                bool hasNew;

                do {
                    hasNew = false;

                    std::set<std::string> newstr;

                    for (auto& s : g.rules[N]) {
                        if (s.find(key) != std::string::npos && s.size() > 1) {
                            newstr.insert(s.substr(0, s.find('$')) + s.substr(s.find('$') + 1, s.size()));
                        }
                    }

                    for (auto& i : newstr)
                        if (g.rules[N].find(i) == g.rules[N].end()) {
                            hasNew = true;
                            break;
                        }

                    g.rules[N].insert(newstr.begin(), newstr.end());
                } while (hasNew);
            }
        }

        key = getLambda(g);
    }
}

void renameElim(grammar& g) {
    for (auto& N : g.nonterminals) {
        if (g.rules[N].size() == 1) {
            std::string s = *(g.rules[N].begin());
            if (s.size() == 1 && g.nonterminals.count(s[0]))
                g.rules[N] = g.rules[s[0]];
        }
    }
}

void redundantElim(grammar& g) {
    std::set<char> access = {g.init};
    bool hasNew;
    do {
        hasNew = false;

        std::set<char> newacc;
        for (auto& key : access)
            for (auto& s : g.rules[key])
                for (auto& c : s)
                    if (g.nonterminals.find(c) != g.nonterminals.end()) newacc.insert(c);
        
        for (auto& i : newacc)
            if (access.find(i) == access.end()) {
                hasNew = true;
                break;
            }

        access.insert(newacc.begin(), newacc.end());
    } while (hasNew);

    std::set<char> elim;
    for (auto& c : g.nonterminals)
        if (access.find(c) == access.end())
            elim.insert(c);

    for (auto& key : g.nonterminals) {
        bool takeOut = true;
        for (auto& s : g.rules[key]) {
            bool allTerms = true;

            for (auto& c : s)
                if (g.nonterminals.find(c) != g.nonterminals.end())
                    allTerms = false;

            if (allTerms) takeOut = false;
        }
        if (takeOut) elim.insert(key);
    }

    for (auto& c : elim) {
        for (auto& key : access) {
            std::set<std::string> selim;

            for (auto& s : g.rules[key])
                if (s.find(c) != std::string::npos)
                    selim.insert(s);

            for (auto& s : selim) {
                g.rules[key].erase(s);
            }
        }

        g.nonterminals.erase(c);
        g.rules.erase(c);
    }
}

void separateTerm(grammar& g) {
    std::set<char> newterms;
    for (auto& key : g.nonterminals)
        if (g.rules[key].size() > 1)
            for (auto& s : g.rules[key]) {
                for (auto& c : s)
                    if (g.terminals.find(c) != g.terminals.end())
                        newterms.insert(c);
            }
    
    for (auto& c : newterms) {
        char x = addNonterminal(g);

        for (auto& key : g.nonterminals) {
            std::set<std::string> aux;
            for (auto& s : g.rules[key]) {
                std::string cpy = replace(s, c, x);
                aux.insert(cpy);
            }
            g.rules[key] = aux;
        }

        g.rules[x].insert(std::string(1, c));
    }
}

void addFinal(grammar& g) {
recheck:
    for (auto& key : g.nonterminals) {
        for (auto& s : g.rules[key]) {
            if (s.size() > 2) {
                char c = addNonterminal(g);
                std::string cpy = s;

                g.rules[c].insert(s.substr(1, s.size()-1));
                cpy.replace(1, cpy.size() - 1, std::string(1, c));
                g.rules[key].erase(s);
                g.rules[key].insert(cpy);

                goto recheck;
            }
        }
    }
}

int main()
{
    grammar g;
    std::fstream f("input.txt", std::ios::in);
    read(g, f);
    lambdaElim(g);
    write(g, std::cout);
}
