#include <iostream>
#include <vector>
#include <cstdint>
#include <atomic>
#include <thread>
#include <mutex>
#include <algorithm>
#include <chrono>
#include <QApplication>
#include <QMainWindow>
#include <QVBoxLayout>
#include <QHBoxLayout>
#include <QGridLayout>
#include <QLabel>
#include <QSpinBox>
#include <QPushButton>
#include <QTableWidget>
#include <QTextEdit>
#include <QHeaderView>
#include <QMessageBox>
#include <QThread>

using namespace std;

// Тип для битовых масок левой и правой долей (предполагаем размер ≤ 64)
using Mask = uint64_t;

// Класс двудольного графа с хранением соседей левых вершин в виде битовых масок
class BipartiteGraph {
private:
    int left_size, right_size;
    vector<Mask> left_neighbors;   // neighbors[u] – битовая маска правых вершин, смежных с u
    Mask right_all_mask;           // маска всех правых вершин (нужна для операций)

public:
    BipartiteGraph(int left, int right) : left_size(left), right_size(right) {
        left_neighbors.resize(left, 0);
        right_all_mask = (right == 64) ? ~Mask(0) : (Mask(1) << right) - 1;
    }

    void addEdge(int u, int v) {
        if (u >= 0 && u < left_size && v >= 0 && v < right_size)
            left_neighbors[u] |= (Mask(1) << v);
    }

    bool hasEdge(int u, int v) const {
        return (left_neighbors[u] >> v) & 1;
    }

    int getLeftSize() const { return left_size; }
    int getRightSize() const { return right_size; }

    // Возвращает маску соседей левой вершины u
    Mask getNeighbors(int u) const { return left_neighbors[u]; }

    // Проверяет, является ли пара (left_mask, right_mask) полной бикликой
    bool isCompleteBiclique(Mask left_mask, Mask right_mask) const {
        if (left_mask == 0 || right_mask == 0) return false;
        Mask m = left_mask;
        while (m) {
            int u = __builtin_ctzll(m);  // индекс первой единицы
            if ((left_neighbors[u] & right_mask) != right_mask)
                return false;
            m &= m - 1;
        }
        return true;
    }

    // Возвращает количество рёбер в графе
    int getEdgeCount() const {
        int cnt = 0;
        for (int u = 0; u < left_size; ++u) {
            cnt += __builtin_popcountll(left_neighbors[u]);
        }
        return cnt;
    }
};

// Генерация всех формальных понятий (максимальных биклик) графа.
// Используется простой перебор всех левых масок с проверкой максимальности.
// Внимание: при L > 20 перебор может быть очень медленным.
class FormalConceptGenerator {
private:
    const BipartiteGraph& graph;
    int L, R;

    // Замыкание: для данного множества левых вершин left_mask вычисляем максимальное
    // множество правых вершин, образующих полную биклику (пересечение соседей).
    Mask closureRight(Mask left_mask) const {
        if (left_mask == 0) return 0;
        Mask result = graph.getNeighbors(__builtin_ctzll(left_mask));
        Mask m = left_mask;
        while (m) {
            int u = __builtin_ctzll(m);
            result &= graph.getNeighbors(u);
            m &= m - 1;
        }
        return result;
    }

    // Проверка, что (A, B) – максимальная биклика (нельзя добавить ни одной левой вершины,
    // сохранив B неизменным). B уже должно быть пересечением соседей A.
    bool isMaximal(Mask A, Mask B) const {
        // Ищем левую вершину вне A, чьи соседи содержат B
        Mask candidates = ~A & ((Mask(1) << L) - 1);
        while (candidates) {
            int v = __builtin_ctzll(candidates);
            if ((graph.getNeighbors(v) & B) == B) {
                return false;
            }
            candidates &= candidates - 1;
        }
        return true;
    }

public:
    FormalConceptGenerator(const BipartiteGraph& g) : graph(g), L(g.getLeftSize()), R(g.getRightSize()) {}

    // Генерирует все формальные понятия (максимальные биклики)
    vector<pair<Mask, Mask>> generateAllConcepts() {
        vector<pair<Mask, Mask>> concepts;
        if (L == 0 || R == 0) return concepts;
        Mask all_left = (L == 64) ? ~Mask(0) : (Mask(1) << L) - 1;
        for (Mask left = 1; left <= all_left; ++left) {
            Mask right = closureRight(left);
            if (right != 0 && isMaximal(left, right)) {
                concepts.emplace_back(left, right);
            }
        }
        return concepts;
    }
};

// Класс для решения задачи покрытия бикликами
class BicliqueCoverSolver {
private:
    const BipartiteGraph& graph;
    int K;                                  // максимальный размер покрытия
    atomic<bool> solution_found;             // флаг, что решение найдено
    vector<vector<pair<Mask, Mask>>> solutions; // накопленные решения
    mutex solutions_mutex;

    // Структура для представления биклики-кандидата
    struct Biclique {
        Mask left;
        Mask right;
        // Для быстрой оценки: сколько рёбер покрывает данная биклика (число |left|*|right|)
        int edgeCount() const {
            return __builtin_popcountll(left) * __builtin_popcountll(right);
        }
    };

    vector<Biclique> candidates;            // список кандидатов (формальные понятия)

    // Проверка, покрывает ли текущий набор биклик все рёбра графа.
    // Используем массив covered_for_left, где для каждой левой вершины хранится маска
    // уже покрытых правых вершин.
    bool coversAllEdges(const vector<Biclique>& cover) const {
        vector<Mask> covered(graph.getLeftSize(), 0);
        for (const auto& bic : cover) {
            Mask left_mask = bic.left;
            // Для всех левых вершин из left_mask добавляем bic.right в покрытые
            while (left_mask) {
                int u = __builtin_ctzll(left_mask);
                covered[u] |= bic.right;
                left_mask &= left_mask - 1;
            }
        }
        // Проверяем, что для каждой левой вершины покрыты все её соседи
        for (int u = 0; u < graph.getLeftSize(); ++u) {
            if ((covered[u] & graph.getNeighbors(u)) != graph.getNeighbors(u))
                return false;
        }
        return true;
    }

    // Оценочная функция нижней границы: сколько ещё биклик минимально нужно,
    // чтобы покрыть оставшиеся рёбра. Используем простую эвристику:
    // максимум по левым вершинам числа непокрытых соседей.
    int lowerBound(const vector<Mask>& covered) const {
        int max_uncovered = 0;
        for (int u = 0; u < graph.getLeftSize(); ++u) {
            Mask uncovered = graph.getNeighbors(u) & ~covered[u];
            int cnt = __builtin_popcountll(uncovered);
            if (cnt > max_uncovered) max_uncovered = cnt;
        }
        return max_uncovered;
    }

    // Рекурсивный поиск с возвратом и эвристиками.
    // current_cover – текущий набор выбранных биклик
    // covered – состояние покрытых правых вершин для каждой левой
    // depth – текущая глубина (размер current_cover)
    // start_idx – индекс, с которого начинаем перебор кандидатов (для избежания повторений)
    void findCoverRecursive(vector<Biclique>& current_cover,
                            vector<Mask>& covered,
                            int depth, int start_idx) {
        if (solution_found.load()) return;
        if (depth > K) return;

        // Проверка полного покрытия
        if (coversAllEdges(current_cover)) {
            if (!solution_found.exchange(true)) {
                lock_guard<mutex> lock(solutions_mutex);
                // Преобразуем Biclique обратно в пары для вывода
                vector<pair<Mask, Mask>> sol;
                for (const auto& bic : current_cover) {
                    sol.emplace_back(bic.left, bic.right);
                }
                solutions.push_back(sol);
            }
            return;
        }

        if (depth == K) return; // нельзя добавлять больше

        // Оценка нижней границы: если даже при оптимальном выборе нужно больше биклик, чем осталось места, отсекаем
        int need = lowerBound(covered);
        if (depth + need > K) return;

        // Перебираем кандидаты, начиная с start_idx
        for (int i = start_idx; i < (int)candidates.size(); ++i) {
            const auto& bic = candidates[i];
            // Можно пропустить биклики, которые не добавляют новых покрытых рёбер (бесполезны)
            bool useful = false;
            Mask left_tmp = bic.left;
            while (left_tmp) {
                int u = __builtin_ctzll(left_tmp);
                if ((covered[u] & bic.right) != bic.right) {
                    useful = true;
                    break;
                }
                left_tmp &= left_tmp - 1;
            }
            if (!useful) continue;

            // Добавляем биклику
            current_cover.push_back(bic);
            // Сохраняем старое состояние для восстановления
            vector<Mask> old_covered = covered;
            left_tmp = bic.left;
            while (left_tmp) {
                int u = __builtin_ctzll(left_tmp);
                covered[u] |= bic.right;
                left_tmp &= left_tmp - 1;
            }

            // Рекурсивный вызов
            findCoverRecursive(current_cover, covered, depth + 1, i + 1);

            // Восстанавливаем состояние
            covered.swap(old_covered);
            current_cover.pop_back();

            if (solution_found.load()) return;
        }
    }

public:
    BicliqueCoverSolver(const BipartiteGraph& g, int k) : graph(g), K(k), solution_found(false) {}

    // Основной метод решения с параллелизацией
    bool solveParallel(int num_threads = 4) {
        // Генерируем формальные понятия (максимальные биклики)
        FormalConceptGenerator gen(graph);
        auto concepts = gen.generateAllConcepts();
        cout << "Найдено максимальных биклик (формальных понятий): " << concepts.size() << endl;

        // Преобразуем в список кандидатов
        candidates.clear();
        for (const auto& p : concepts) {
            candidates.push_back({p.first, p.second});
        }

        // Если граф не содержит рёбер, покрытие пустое
        if (graph.getEdgeCount() == 0) {
            solutions.clear();
            solutions.push_back({});
            return true;
        }

        if (candidates.empty()) return false;

        // Сортируем кандидатов по убыванию числа покрываемых рёбер (эвристика для ускорения)
        sort(candidates.begin(), candidates.end(),
             [](const Biclique& a, const Biclique& b) {
                 return a.edgeCount() > b.edgeCount();
             });

        // Поиск для размеров от 1 до K
        for (int k = 1; k <= K; ++k) {
            cout << "Проверка для K = " << k << endl;
            solution_found.store(false);
            solutions.clear();

            vector<thread> threads;
            int cand_per_thread = max(1, (int)candidates.size() / num_threads);

            for (int t = 0; t < num_threads; ++t) {
                int start = t * cand_per_thread;
                int end = (t == num_threads - 1) ? candidates.size() : (t + 1) * cand_per_thread;

                threads.emplace_back([this, start, end, k]() {
                    for (int i = start; i < end && !solution_found.load(); ++i) {
                        vector<Biclique> cover;
                        cover.push_back(candidates[i]);
                        vector<Mask> covered(graph.getLeftSize(), 0);
                        // Инициализируем covered добавлением первой биклики
                        Mask left_tmp = candidates[i].left;
                        while (left_tmp) {
                            int u = __builtin_ctzll(left_tmp);
                            covered[u] |= candidates[i].right;
                            left_tmp &= left_tmp - 1;
                        }
                        findCoverRecursive(cover, covered, 1, i + 1);
                    }
                });
            }

            for (auto& th : threads) th.join();

            if (solution_found.load()) {
                cout << "Найдено покрытие размером " << k << endl;
                // Решения уже сохранены в solutions
                return true;
            }
        }
        return false;
    }

    // Получить найденные решения
    vector<vector<pair<Mask, Mask>>> getSolutions() const {
        return solutions;
    }
};

// ==================== GUI часть ====================

#include <QMainWindow>
#include <QVBoxLayout>
#include <QHBoxLayout>
#include <QGridLayout>
#include <QLabel>
#include <QSpinBox>
#include <QPushButton>
#include <QTableWidget>
#include <QTextEdit>
#include <QHeaderView>
#include <QMessageBox>
#include <QThread>
#include <QCoreApplication>
#include <streambuf>

// Класс для перенаправления std::cout в QTextEdit
class LogStream : public std::streambuf {
public:
    LogStream(QTextEdit* textEdit) : textEdit(textEdit) {}

protected:
    virtual int_type overflow(int_type c) override {
        if (c != EOF) {
            buffer += static_cast<char>(c);
            if (c == '\n') {
                flushBuffer();
            }
        }
        return c;
    }

    virtual std::streamsize xsputn(const char* s, std::streamsize n) override {
        for (std::streamsize i = 0; i < n; ++i) {
            if (s[i] == '\n') {
                buffer += s[i];
                flushBuffer();
            } else {
                buffer += s[i];
            }
        }
        return n;
    }

private:
    void flushBuffer() {
        if (!buffer.empty()) {
            QMetaObject::invokeMethod(textEdit, "append", Qt::QueuedConnection,
                                      Q_ARG(QString, QString::fromStdString(buffer)));
            buffer.clear();
        }
    }

    QTextEdit* textEdit;
    std::string buffer;
};

// Поток для выполнения вычислений
class SolverThread : public QThread {
    Q_OBJECT
public:
    SolverThread(BicliqueCoverSolver* solver, QObject* parent = nullptr)
        : QThread(parent), solver(solver) {}

    void run() override {
        result = solver->solveParallel();
        solutions = solver->getSolutions();
    }

    bool getResult() const { return result; }
    vector<vector<pair<Mask, Mask>>> getSolutions() const { return solutions; }

signals:
    void finished();

private:
    BicliqueCoverSolver* solver;
    bool result;
    vector<vector<pair<Mask, Mask>>> solutions;
};

// Главное окно
class MainWindow : public QMainWindow {
    Q_OBJECT
public:
    MainWindow(QWidget* parent = nullptr) : QMainWindow(parent) {
        setWindowTitle("Покрытие двудольного графа бикликами");

        QWidget* central = new QWidget(this);
        setCentralWidget(central);
        QVBoxLayout* mainLayout = new QVBoxLayout(central);

        // Верхняя панель: размеры долей и K
        QHBoxLayout* topLayout = new QHBoxLayout();
        topLayout->addWidget(new QLabel("Левая доля (L):"));
        leftSpin = new QSpinBox();
        leftSpin->setRange(1, 64);
        leftSpin->setValue(3);
        topLayout->addWidget(leftSpin);

        topLayout->addWidget(new QLabel("Правая доля (R):"));
        rightSpin = new QSpinBox();
        rightSpin->setRange(1, 64);
        rightSpin->setValue(3);
        topLayout->addWidget(rightSpin);

        topLayout->addWidget(new QLabel("Макс. размер K:"));
        kSpin = new QSpinBox();
        kSpin->setRange(1, 100);
        kSpin->setValue(3);
        topLayout->addWidget(kSpin);

        QPushButton* initTableBtn = new QPushButton("Инициализировать таблицу рёбер");
        topLayout->addWidget(initTableBtn);
        topLayout->addStretch();
        mainLayout->addLayout(topLayout);

        // Таблица для рёбер
        table = new QTableWidget(this);
        table->setColumnCount(2);
        QStringList headers = {"u (левая)", "v (правая)"};
        table->setHorizontalHeaderLabels(headers);
        table->horizontalHeader()->setSectionResizeMode(QHeaderView::Stretch);
        mainLayout->addWidget(table);

        // Кнопка Solve
        QPushButton* solveBtn = new QPushButton("Решить");
        mainLayout->addWidget(solveBtn);

        // Текстовое поле для вывода
        logText = new QTextEdit(this);
        logText->setReadOnly(true);
        logText->setFontFamily("Courier");
        mainLayout->addWidget(logText);

        // Подключение сигналов
        connect(initTableBtn, &QPushButton::clicked, this, &MainWindow::initTable);
        connect(solveBtn, &QPushButton::clicked, this, &MainWindow::solve);

        // Инициализируем таблицу по умолчанию
        initTable();

        // Настройка перенаправления cout
        logStream = new LogStream(logText);
        oldCoutBuf = cout.rdbuf(logStream);
    }

    ~MainWindow() {
        cout.rdbuf(oldCoutBuf);
        delete logStream;
    }

private slots:
    void initTable() {
        int L = leftSpin->value();
        int R = rightSpin->value();
        table->setRowCount(L * R); // максимально возможное число рёбер
        // Очистить ячейки
        for (int i = 0; i < table->rowCount(); ++i) {
            for (int j = 0; j < 2; ++j) {
                QTableWidgetItem* item = table->item(i, j);
                if (!item) {
                    item = new QTableWidgetItem();
                    table->setItem(i, j, item);
                }
                item->setText("");
            }
        }
        // Можно заполнить подсказками для первых L*R строк, но оставим пустыми
    }

    void solve() {
        // Сбор данных из GUI
        int L = leftSpin->value();
        int R = rightSpin->value();
        int K = kSpin->value();

        // Создаём граф
        BipartiteGraph graph(L, R);

        // Читаем рёбра из таблицы
        bool ok;
        int edgesAdded = 0;
        for (int row = 0; row < table->rowCount(); ++row) {
            QString leftStr = table->item(row, 0) ? table->item(row, 0)->text() : "";
            QString rightStr = table->item(row, 1) ? table->item(row, 1)->text() : "";
            if (leftStr.isEmpty() || rightStr.isEmpty()) continue;

            int u = leftStr.toInt(&ok);
            if (!ok || u < 0 || u >= L) {
                QMessageBox::warning(this, "Ошибка", QString("Некорректная левая вершина в строке %1: %2").arg(row+1).arg(leftStr));
                return;
            }
            int v = rightStr.toInt(&ok);
            if (!ok || v < 0 || v >= R) {
                QMessageBox::warning(this, "Ошибка", QString("Некорректная правая вершина в строке %1: %2").arg(row+1).arg(rightStr));
                return;
            }
            graph.addEdge(u, v);
            edgesAdded++;
        }

        if (edgesAdded == 0 && graph.getEdgeCount() == 0) {
            QMessageBox::information(this, "Информация", "Граф не содержит рёбер. Покрытие пустое.");
            return;
        }

        // Создаём решатель
        BicliqueCoverSolver solver(graph, K);

        // Запускаем в отдельном потоке
        solverThread = new SolverThread(&solver, this);
        connect(solverThread, &SolverThread::finished, this, &MainWindow::onSolverFinished);
        solverThread->start();

        // Блокируем кнопки во время вычислений
        leftSpin->setEnabled(false);
        rightSpin->setEnabled(false);
        kSpin->setEnabled(false);
        table->setEnabled(false);
    }

    void onSolverFinished() {
        if (!solverThread) return;

        bool result = solverThread->getResult();
        auto solutions = solverThread->getSolutions();

        logText->append("\n=== РЕЗУЛЬТАТ ===");
        if (result) {
            logText->append("Покрытие существует.");
            if (!solutions.empty()) {
                const auto& sol = solutions[0];
                logText->append(QString("Покрытие размером %1:").arg(sol.size()));
                for (size_t i = 0; i < sol.size(); ++i) {
                    Mask left = sol[i].first;
                    Mask right = sol[i].second;
                    QString leftStr, rightStr;
                    Mask ltmp = left;
                    while (ltmp) {
                        int u = __builtin_ctzll(ltmp);
                        leftStr += QString::number(u) + " ";
                        ltmp &= ltmp - 1;
                    }
                    Mask rtmp = right;
                    while (rtmp) {
                        int v = __builtin_ctzll(rtmp);
                        rightStr += QString::number(v) + " ";
                        rtmp &= rtmp - 1;
                    }
                    logText->append(QString("  K%1: левая доля = { %2}, правая доля = { %3}")
                                        .arg(i+1).arg(leftStr).arg(rightStr));
                }
            }
        } else {
            logText->append("Покрытие не существует для заданного K.");
        }

        // Разблокируем элементы управления
        leftSpin->setEnabled(true);
        rightSpin->setEnabled(true);
        kSpin->setEnabled(true);
        table->setEnabled(true);

        solverThread->deleteLater();
        solverThread = nullptr;
    }

private:
    QSpinBox* leftSpin;
    QSpinBox* rightSpin;
    QSpinBox* kSpin;
    QTableWidget* table;
    QTextEdit* logText;
    LogStream* logStream;
    std::streambuf* oldCoutBuf;
    SolverThread* solverThread = nullptr;
};

// Необходимо для moc
#include <QMetaObject>
// Определяем сигналы/слоты вручную (можно вынести в отдельный файл, но для простоты оставим здесь)
// Обычно moc-файл генерируется автоматически. Для компиляции нужно будет запустить moc.

int main(int argc, char *argv[]) {
    QApplication app(argc, argv);
    MainWindow w;
    w.show();
    return app.exec();
}

#include "main.moc" // для корректной обработки сигналов/слотов при сборке с qmake
