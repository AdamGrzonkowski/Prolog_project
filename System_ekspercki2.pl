% Autorzy:  Adam S. Grzonkowski, Miko³aj Trawiñskki
% Data: 2015-06-13
% System ekspercki diagnozujacy awarie sprzetowa komputera
% Rozpatrujemy tu sytuacje podstawowych usterek, uniemozliwiajacych prace

%----------------------------------------------------%
%              Baza danych / baza wiedzy             %
%----------------------------------------------------%


rule((rozwiazanie(Advice) :- (wadliwy_komponent(X),rozwiazanie(X, Advice))), 100).

% Zasady wykrywajace awarie danego komponentu na podstawie awarii danej funkcjonalnosci
rule((wadliwy_komponent(procesor) :- (wadliwa_funkcjonalnosc(praca_procesora), not(wykonuje_programy))),60).
rule((wadliwy_komponent(pamiec_ram) :- (wadliwa_funkcjonalnosc(praca_systemu), not(dziala_szybko))),75).
rule((wadliwy_komponent(dysk) :- (wadliwa_funkcjonalnosc(praca_dysku), wlacza_sie, dziala_szybko)),80).
rule((wadliwy_komponent(zasilanie) :- (wadliwa_funkcjonalnosc(uruchamianie))),90).
rule((wadliwy_komponent(karta_graficzna) :- (wadliwa_funkcjonalnosc(obraz),not(widzisz_obraz_na_innym_monitorze))),60).
rule((wadliwy_komponent(matryca) :- (wadliwa_funkcjonalnosc(obraz),widzisz_obraz_na_innym_monitorze)),85).

% Zasady wykrywajace usterke danej funkcjonalnosci
rule((wadliwa_funkcjonalnosc(uruchamianie) :- (not(wlacza_sie))),90).
rule((wadliwa_funkcjonalnosc(praca_dysku) :- (not(wczytuje_system))),60).
rule((wadliwa_funkcjonalnosc(praca_dysku) :- (wczytuje_system,not(zapisuje/pobiera_dane))),80).
rule((wadliwa_funkcjonalnosc(praca_systemu) :- (wlacza_sie, wczytuje_system, wykonuje_programy)),80).
rule((wadliwa_funkcjonalnosc(praca_procesora) :- (wlacza_sie, not(dziala_szybko))),70).
rule((wadliwa_funkcjonalnosc(obraz) :- (wlacza_sie, not(widzisz_obraz))),70).

% Proponowane rozwiazania
rule(rozwiazanie(zasilanie, 'Podlacz komputer do zasilania, sprawdz kabel zasilajacy i zasilacz.'),100).
rule(rozwiazanie(procesor, 'Zmien paste termoprzewodzaca przy procesorze, przeczysc uklad chlodzenia.'),100).
rule(rozwiazanie(pamiec_ram, 'Sprawdz obciazenie pamieci RAM za pomoca mened¿era zadañ. Wylacz programy zuzywajace najwiecej pamieci. Wyjmij i wloz kosci RAM.'),100).
rule(rozwiazanie(dysk, 'Wykonaj sprawdzanie dysku w poszukiwaniu bad sectorow. Sprawdz S.M.A.R.T. dysku, wykonaj kopie zapasowa, wyczysc dysk ze zbednych plikow.'),100).
rule(rozwiazanie(karta_graficzna, 'Sprawdz swoja karte graficzna. Docisnij tasmy. Wybrzuszenia na kondesatorach oznaczaja koniecznosc wymiany.'),100).
rule(rozwiazanie(matryca, 'Sprawdz czy tasma matrycy jest podlaczona do plyty glownej. Jezeli tak, wymien matryce.'),100).

% Pytania do uzytkownika systemu
pytanie(wlacza_sie).
pytanie(wczytuje_system).
pytanie(zapisuje/pobiera_dane).
pytanie(wykonuje_programy).
pytanie(dziala_szybko).
pytanie(widzisz_obraz).
pytanie(widzisz_obraz_na_innym_monitorze).
pytanie(podlaczone_urzadzenia_peryferyjne_dzialaja).


%----------------------------------------------------%
%           Logika programu - program g³ówny         %
%----------------------------------------------------%
% Program wykonywany za pomoca polecenia 'wykonajProgram.'.
wykonajProgram :- wykonajProgram(rozwiazanie(_),_), nl.

% Gdy za malo informacji
wykonajProgram :- retractall(known(_,_)), write('Za malo informacji w celu wykonania diagnozy.'), nl.

% Domyslne wywolanie
wykonajProgram(Goal, CF) :-
 retractall(known(_,_)), wyswietl_instrukcje, wykonajProgram(Goal, CF, [], 25),  % ustawiamy 25 jako wartosc progowa dla naszego CF
 write(Goal), write(' z prawdopodobienstwem '), write(CF),write('%.').

% Gdy w bazie odpowiedzi mamy ju¿ odpowiedŸ na dane pytanie
wykonajProgram(Goal, CF, _, Threshold) :- known(Goal, CF),!, powyzej_progu(CF, Threshold).

% Gdy mamy negacje (cel poprzedzony instrukcja "not")
wykonajProgram( not(Goal), CF, Rules, Threshold) :- !,
   odwroc_prog(Threshold, New_threshold),
   wykonajProgram(Goal, CF_goal, Rules, New_threshold),
   negacja_cf(CF_goal, CF).
   
% Gdy mamy dwie zmienne, ktore sa ze soba w interakcji i musza byc wykonane w tym samym czasie
wykonajProgram((Goal_1,Goal_2), CF, Rules, Threshold) :- !,
 wykonajProgram(Goal_1, CF_1, Rules, Threshold),
 powyzej_progu(CF_1, Threshold),
 wykonajProgram(Goal_2, CF_2, Rules, Threshold),
 powyzej_progu(CF_2, Threshold),
 koniunkcja_cf(CF_1, CF_2, CF).
 
% Metoda backchain na regule w bazie wiedzy
wykonajProgram(Goal, CF, Rules, Threshold) :-
 rule((Goal :- (Premise)), CF_rule),
 wykonajProgram(Premise, CF_premise,
  [rule((Goal :- Premise), CF_rule)|Rules], Threshold),
 rule_cf(CF_rule, CF_premise, CF),
 powyzej_progu(CF, Threshold).
 
% Dodanie faktu do bazy wiedzy.
wykonajProgram(Goal, CF, _, Threshold) :-
 rule(Goal, CF),
 powyzej_progu(CF, Threshold).
 
% Pytanie uzytkownika.
wykonajProgram(Goal, CF, Rules, Threshold) :-
  pytanie(Goal),
  zapytaj(Goal, CF, Rules),!,
  assert(known(Goal, CF)),
  powyzej_progu(CF, Threshold).
 
 
%----------------------------------------------------%
% Instrukcje obslugujace interakcje z uzytkownikiem  %
%----------------------------------------------------%

zapytaj(Goal, CF, Rules) :-
 nl,write('Czy prawda jest, ze '), write(Goal),
 write('? '), nl,
 read(Answer),
 odpowiedz(Answer,Goal, CF, Rules).

% Uzytkownik wpisuje poprawna wartosc CF
odpowiedz(CF, _, CF, _) :- number(CF), CF =< 100, CF >= -100.

% Odpowiedz "n"
odpowiedz(n, _, -100, _).

% Odpowiedz "t"
odpowiedz(t, _, 100, _).

% Wylaczenie programu
odpowiedz(end,_, _, _) :- write(' Dziekujemy za skorzystanie z naszego systemu.'),
                        nl, abort.

% Obsluga niezdefiniowanej wartosci, wpisanej przez uzytkownika
odpowiedz(_, Goal,CF, Rules) :-
 write('Nierozponana wartosc. Sprawdz w instrukcji poczatkowej, co wpisac.'),nl,
 zapytaj(Goal, CF, Rules).

% Wyswietl instrukcje dla uzytkownika
wyswietl_instrukcje :- nl,
 write('System ekspercki pomagajacy znalezc usterke komputera.'), nl,
 write('Wpisz "t." lub "n.", jezeli jestes pewien odpowiedzi.'), nl,
 write('Wpisz liczbe z przedzialu -100 do 100, aby okreslic jak bardzo prawdopodobne jest dane zdarzenie.'), nl,
 write('-100: na pewno nie wystepuje, a 100: na pewno wystepuje.'), nl,
 write('Wpisujac end. mozesz przerwac diagnoze.'), nl.
 
 
%----------------------------------------------------%
% Instrukcje obslugujace przeliczanie CF w oparciu   %
%          o sposób przeliczania CF w MYCIN          %
%----------------------------------------------------%

% Negacja CF
negacja_cf(CF, Negated_CF) :- Negated_CF is -1 * CF.

% Gdy mamy dwa laczne predykaty, zwroc CF mniejszego
koniunkcja_cf(A, B, A) :- A =< B.
koniunkcja_cf(A, B, B) :- B < A.

% Obliczamy CF naszego wniosku, w przypadku, gdy fakt nie jest na 100% falszem lub prawda
rule_cf(CF_rule, CF_premise, CF) :- CF is CF_rule * CF_premise/100.

% Jezeli T ma wartosc dodatnia, to udowadniamy prawde.
% Jezeli F ma wartosc ujemna, to udowadniamy falsz.
powyzej_progu(CF, T) :- T >= 0, CF >= T.
powyzej_progu(CF, T) :- T < 0, CF =< T.

% Gdy udowadniamy not(x), to zmieniamy te dowody x ktore nie dowodza falszu, na wartosci przeciwne
odwroc_prog(Threshold, New_threshold) :- New_threshold is -1 * Threshold.