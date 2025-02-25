DROP TABLE haus;
DROP TABLE baum;

CREATE TABLE haus (
    addrID int,
    name varchar(255)
);

CREATE TABLE baum (
    ortID int,
    art varchar(255)
);

INSERT INTO haus (addrID, name) VALUES (0, 'toll');
INSERT INTO haus (addrID, name) VALUES (1, 'toll');
INSERT INTO haus (addrID, name) VALUES (2, 'schön');
INSERT INTO haus (addrID, name) VALUES (3, 'gigantisch');

INSERT INTO baum (ortID, art) VALUES (0, 'toll');
INSERT INTO baum (ortID, art) VALUES (1, 'schön');
INSERT INTO baum (ortID, art) VALUES (2, 'riesig');
INSERT INTO baum (ortID, art) VALUES (3, 'riesig');
INSERT INTO baum (ortID, art) VALUES (4, 'toll');